from typing import Dict

import dwavebinarycsp
from dwavebinarycsp.factories import multiplication_circuit

from bit_transformation.configurations import Config
from bit_transformation.bit_penalty_models import get_model
from tools import *
from qword import QWord
import dimod
from bit_transformation.more_gates.xnor import get_XNOR
from bit_transformation.more_gates.xor import get_XOR
import re


def get_qubit_value(qubit_name: int, qubits_to_fix: Dict[int, int]) -> Optional[int]:
    if qubit_name in qubits_to_fix.keys():
        return qubits_to_fix[qubit_name]
    return None

def separate_constants(qubit_names: List[int], qubits_to_fix: Dict[int, int]) -> (List[int], List[int]):
    constant_names = []
    non_constant_names = []

    for name in qubit_names:
        if name in qubits_to_fix.keys():
            constant_names.append(name)
        else:
            non_constant_names.append(name)

    return constant_names, non_constant_names

def get_constant_bits_value(constant_names: List[int], qubits_to_fix: Dict[int, int], gate_name: str) -> Optional[int]:

    for name in constant_names:
        value = qubits_to_fix[name]
        if gate_name == AND:
            if value == 0:
                return 0
        elif gate_name == OR:
            if value == 1:
                return 1
        else:
            raise Exception("not excepted gate called at tools.get_constant_bits_value:", gate_name)
    return None

def get_model_single_var(value):
    if value == 0:
        linear_coeff = 2
        bias = 0
    elif value == 1:
        linear_coeff = -2
        bias = 2
    else:
        raise Exception("getting model for single variable failed. Value is not binary.")

    return linear_coeff, bias

class InputPropagationFile:
    file = None

    @staticmethod
    def write_rule(rule_name, target, operands, qubits_to_fix):
        if rule_name == QUOTIENT or rule_name == REMAINDER:
            line = f"{rule_name}"
            for t in target:
                line += f" {t}"
            for operand in operands:
                line += f" {operand}"
            line += "\n"
            InputPropagationFile.file.write(line)
        else:
            value_target = get_qubit_value(target, qubits_to_fix)
            if value_target is None:
                line = f"{rule_name} {target}"
                for operand in operands:
                    line += f" {operand}"
                line += "\n"
                InputPropagationFile.file.write(line)
            else:
                qubits_to_fix[target] = value_target

    @staticmethod
    def close_file():
        InputPropagationFile.file.close()

    @staticmethod
    def open_file(output_dir):
        InputPropagationFile.file = open(f"{output_dir}input_propagation.unicorn", "w")


def optimized_bits_nand(bits: List[int], bqm: dimod.BinaryQuadraticModel, current_n: int,
                        qubits_to_fix: Dict[int, int]) -> QWord:

    raise Exception("this function is not optimized, and I was not expecting to call it.")

    #assert len(_bits) >= 2

    #bits = _bits#[::-1]  # get_more_constants_first(bits, qubits_to_fix,0)

    value_bit0 = get_qubit_value(bits[0], qubits_to_fix)
    value_bit1 = get_qubit_value(bits[1], qubits_to_fix)

    intermediate_result = GlobalIndexer.get_name_index()
    decision_variables = [bits[0], bits[1], intermediate_result]
    model, _ = get_model(Config.NAND, decision_variables)
    # if value_bit0 is not None and value_bit1 is not None:
    #     qubits_to_fix[intermediate_result] = not (value_bit0 and value_bit1)
    # elif value_bit0 == 0 or value_bit1 == 0:
    #     qubits_to_fix[intermediate_result] = 1
    InputPropagationFile.write_rule(NAND, intermediate_result, [bits[0], bits[1]], qubits_to_fix)
    bqm.update(model)

    for bit in bits[2:]:
        prev_intermediate = intermediate_result
        value_bit0 = get_qubit_value(bit, qubits_to_fix)
        value_bit1 = get_qubit_value(prev_intermediate, qubits_to_fix)

        intermediate_result = get_qubit_name()
        decision_variables = [bit, prev_intermediate, intermediate_result]
        model, _ = get_model(Config.NAND, decision_variables)
        # if value_bit0 is not None and value_bit1 is not None:
        #     qubits_to_fix[intermediate_result] = not (value_bit0 and value_bit1)
        # elif value_bit0 == 0 or value_bit1 == 0:
        #     qubits_to_fix[intermediate_result] = 1
        InputPropagationFile.write_rule(NAND, intermediate_result, [bit, prev_intermediate], qubits_to_fix)
        bqm.update(model)

    qword_result = QWord(1)
    qword_result.append_state([intermediate_result], current_n)
    return qword_result


def optimized_bitwise_and(bitset1: List[int], bitset2: List[int], current_n: int, bqm: dimod.BinaryQuadraticModel,
                          qubits_to_fix: Dict[int, int]) -> QWord:
    assert len(bitset1) == len(bitset2)
    result_bitset = []
    for (bit1, bit2) in zip(bitset1, bitset2):

        value_bit1 = get_qubit_value(bit1, qubits_to_fix)
        value_bit2 = get_qubit_value(bit2, qubits_to_fix)

        if value_bit1 == 1 and value_bit2 is None:
            resbit = bit2
        elif value_bit1 is None and value_bit2 == 1:
            resbit = bit1
        else:
            resbit = get_qubit_name()
            model, _ = get_model(Config.AND, [bit1, bit2, resbit])
            bqm.update(model)
            if value_bit1 is not None and value_bit2 is not None:
                qubits_to_fix[resbit] = value_bit1 and value_bit2
            elif value_bit1 == 0 or value_bit2 == 0:
                qubits_to_fix[resbit] = 0
            InputPropagationFile.write_rule(R_AND, resbit, [bit1, bit2], qubits_to_fix)
        result_bitset.append(resbit)
    result_qword = QWord(len(bitset1))
    result_qword.append_state(result_bitset, current_n)
    return result_qword


def optimized_bitwise_not(bitset1: List[int], current_n, bqm: dimod.BinaryQuadraticModel,
                          qubits_to_fix: Dict[int, int]) -> QWord:
    assert len(bitset1) > 0

    result_qword = QWord(len(bitset1))
    result_qword.create_state(bqm, current_n)

    for (bit1, resbit) in zip(bitset1, result_qword[current_n]):
        model, _ = get_model(Config.NOT, [bit1, resbit])
        bqm.update(model)
        bit1_value = get_qubit_value(bit1, qubits_to_fix)
        if bit1_value is not None:
            qubits_to_fix[resbit] = not qubits_to_fix[bit1]
        InputPropagationFile.write_rule(R_NOT, resbit, [bit1], qubits_to_fix)
    return result_qword


def optimized_get_twos_complement(bitset1: List[int], current_n: int, bqm: dimod.BinaryQuadraticModel,
                                  qubits_to_fix: Dict[int, int]) -> QWord:
    # flip bits
    flipped_qword = optimized_bitwise_not(bitset1, current_n, bqm, qubits_to_fix)

    # sum one
    qubitset_one = QWord(len(bitset1))
    qubitset_one.create_state(bqm, current_n)

    # fix this value in the bqm. We know it equals 1.
    for (index, name) in enumerate(qubitset_one[current_n]):
        if index == 0:
            qubits_to_fix[name] = 1
        else:
            qubits_to_fix[name] = 0
        linear_coeff, add_offset = get_model_single_var(qubits_to_fix[name])
        bqm.offset += add_offset
        bqm.add_linear(name, linear_coeff)

    result = optimized_bitwise_add(flipped_qword[current_n], qubitset_one[current_n], current_n, bqm, qubits_to_fix)

    return result


def optimized_unsigned_less_than(bitset1: List[int], bitset2: List[int], current_n: int,
                                 bqm: dimod.BinaryQuadraticModel,
                                 qubits_to_fix: Dict[int, int]) -> QWord:
    random_name1 = GlobalIndexer.get_name_index()
    copy_bitset1 = bitset1.copy()
    copy_bitset1.append(random_name1)
    qubits_to_fix[random_name1] = 0
    linear_coeff, add_offset = get_model_single_var(0)
    bqm.add_variable(random_name1, linear_coeff)
    bqm.offset += add_offset

    random_name2 = GlobalIndexer.get_name_index()  # add an extra qubit to take the twos complement
    copy_bitset2 = bitset2.copy()
    copy_bitset2.append(random_name2)
    qubits_to_fix[random_name2] = 0
    linear_coeff, add_offset = get_model_single_var(0)
    bqm.add_variable(random_name2, linear_coeff)
    bqm.offset += add_offset

    qword_2c_bitset2 = optimized_get_twos_complement(copy_bitset2, current_n, bqm, qubits_to_fix)
    bitset2_2c = qword_2c_bitset2[current_n]

    assert len(copy_bitset1) == len(bitset2_2c)

    subtraction_res = optimized_bitwise_add(copy_bitset1, bitset2_2c, current_n, bqm, qubits_to_fix)
    qubitset_subs_res = subtraction_res[current_n]

    qword_result = QWord(1)
    qword_result.append_state([qubitset_subs_res[-1]], current_n)  # if most significant it is turned on then result
    # is negative
    return qword_result


def optimized_unsigned_greater_than(bitset1: List[int], bitset2: List[int], current_n: int,
                                    bqm: dimod.BinaryQuadraticModel,
                                    qubits_to_fix: Dict[int, int]) -> QWord:
    return optimized_unsigned_less_than(bitset2, bitset1, current_n, bqm, qubits_to_fix)


def optimized_unsigned_lte(bitset1: List[int], bitset2: List[int], current_n: int, bqm: dimod.BinaryQuadraticModel,
                           qubits_to_fix: Dict[int, int]) -> QWord:
    is_gt_qword = optimized_unsigned_less_than(bitset1, bitset2, current_n, bqm, qubits_to_fix)
    is_gt_qubit = is_gt_qword[current_n][0]

    is_equal_qword = optimized_is_equal(bitset1, bitset2, current_n, bqm, qubits_to_fix)
    is_equal_qubit = is_equal_qword[current_n][0]

    value_gt_qubit = get_qubit_value(is_gt_qubit, qubits_to_fix)
    value_equal_qubit = get_qubit_value(is_equal_qubit, qubits_to_fix)

    qword_result = QWord(1)
    if value_gt_qubit == 0 and value_equal_qubit is None:
        qword_result.append_state([is_equal_qubit], current_n)
    elif value_gt_qubit is None and value_equal_qubit == 0:
        qword_result.append_state([is_gt_qubit], current_n)
    else:
        random_name = GlobalIndexer.get_name_index()
        model, _ = get_model(Config.OR, [is_gt_qubit, is_equal_qubit, random_name])
        bqm.update(model)

        if value_gt_qubit is not None and value_equal_qubit is not None:
            qubits_to_fix[random_name] = value_gt_qubit or value_equal_qubit
        elif value_gt_qubit == 1 or value_equal_qubit == 1:
            qubits_to_fix[random_name] = 1
        InputPropagationFile.write_rule(OR, random_name, [is_gt_qubit, is_equal_qubit], qubits_to_fix)
        qword_result.append_state([random_name], current_n)
    return qword_result


def optimized_unsigned_gte(bitset1: List[int], bitset2: List[int], current_n: int, bqm: dimod.BinaryQuadraticModel,
                           qubits_to_fix: Dict[int, int]) -> QWord:
    return optimized_unsigned_lte(bitset2, bitset1, current_n, bqm, qubits_to_fix)


def optimized_half_adder(input1: int, input2: int, bqm: dimod.BinaryQuadraticModel, qubits_to_fix: Dict[int, int]):
    value_input1 = get_qubit_value(input1, qubits_to_fix)
    value_input2 = get_qubit_value(input2, qubits_to_fix)

    if not (value_input1 is None) and not (value_input2 is None):
        carry = get_qubit_name()
        result = get_qubit_name()
        qubits_to_fix[carry] = value_input1 and value_input2
        qubits_to_fix[result] = (value_input1 + value_input2) % 2

        linear_carry, offset_carry = get_model_single_var(qubits_to_fix[carry])
        bqm.add_variable(carry, linear_carry)
        bqm.offset += offset_carry

        linear_result, offset_result = get_model_single_var(qubits_to_fix[result])
        bqm.add_variable(result, linear_result)
        bqm.offset += offset_result
    elif value_input1 is not None and value_input2 is None:
        if value_input1 == 0:
            carry = get_qubit_name()
            qubits_to_fix[carry] = 0
            linear_carry, offset_carry = get_model_single_var(qubits_to_fix[carry])
            bqm.add_variable(carry, linear_carry)
            bqm.offset += offset_carry
            result = input2
        else:
            carry = input2
            result = get_qubit_name()
            model, _ = get_model(Config.NOT, [input2, result])
            bqm.update(model)
            InputPropagationFile.write_rule(R_NOT, result, [input2], qubits_to_fix)
    elif value_input1 is None and value_input2 is not None:
        if value_input2 == 0:
            carry = get_qubit_name()
            qubits_to_fix[carry] = 0
            linear_carry, offset_carry = get_model_single_var(qubits_to_fix[carry])
            bqm.add_variable(carry, linear_carry)
            bqm.offset += offset_carry
            result = input1
        else:
            carry = input1
            result = get_qubit_name()
            model, _ = get_model(Config.NOT, [input1, result])
            bqm.update(model)
            InputPropagationFile.write_rule(R_NOT, result, [input1], qubits_to_fix)
    else:
        # no constant propagation
        carry = get_qubit_name()
        result = get_qubit_name()

        def get_half_adder():
            linear = {'aux0': 4.0, carry: 4.0, input1: 2.0, input2: 2.0, result: 2.0}
            quadratic = {(carry, 'aux0'): 4.0,
                         (input1, 'aux0'): -4.0,
                         (input1, carry): -4.0,
                         (input2, 'aux0'): 4.0,
                         (input2, carry): -4.0,
                         (input2, input1): 0.0,
                         (result, 'aux0'): -4.0,
                         (result, carry): 4.0,
                         (result, input1): 0.0,
                         (result, input2): -4.0}
            return dimod.BinaryQuadraticModel(linear, quadratic, dimod.BINARY)

        temp_bqm = get_half_adder()
        aux0 = GlobalIndexer.get_name_index()
        temp_bqm.relabel_variables({'aux0': aux0})
        InputPropagationFile.write_rule(AUX_HALF_ADDER, aux0, [input1, input2], qubits_to_fix)
        InputPropagationFile.write_rule(CARRY_HALF_ADDER, carry, [input1, input2], qubits_to_fix)
        InputPropagationFile.write_rule(RESULT_HALF_ADDER, result, [input1, input2], qubits_to_fix)
        bqm.update(temp_bqm)
    return carry, result


def optimized_full_adder(input1: int, input2: int, input3: int, bqm: dimod.BinaryQuadraticModel,
                         qubits_to_fix: Dict[int, int]):
    value_input1 = get_qubit_value(input1, qubits_to_fix)
    value_input2 = get_qubit_value(input2, qubits_to_fix)
    value_input3 = get_qubit_value(input3, qubits_to_fix)

    def are_there_2_known_variables():
        if value_input1 is not None and value_input2 is not None and value_input3 is None:
            return True

        if value_input1 is not None and value_input2 is None and value_input3 is not None:
            return True

        if value_input1 is None and value_input2 is not None and value_input3 is not None:
            return True

        return False

    def get_variables_names():
        known = []
        unknown = []

        if value_input1 is None:
            unknown.append(input1)
        else:
            known.append(input1)

        if value_input2 is None:
            unknown.append(input2)
        else:
            known.append(input2)

        if value_input3 is None:
            unknown.append(input3)
        else:
            known.append(input3)

        return known, unknown

    if value_input1 is not None and value_input2 is not None and value_input3 is not None:
        result = get_qubit_name()
        carry = get_qubit_name()
        qubits_to_fix[carry] = (value_input1 + value_input2 + value_input3) > 1
        qubits_to_fix[result] = (value_input1 + value_input2 + value_input3) % 2

        linear_carry, offset_carry = get_model_single_var(qubits_to_fix[carry])
        bqm.add_variable(carry, linear_carry)
        bqm.offset += offset_carry

        linear_result, offset_result = get_model_single_var(qubits_to_fix[result])
        bqm.add_variable(result, linear_result)
        bqm.offset += offset_result
    elif are_there_2_known_variables():
        not_none_vars, none_vars = get_variables_names()
        xi = not_none_vars[0]
        xj = not_none_vars[1]
        xk = none_vars[0]

        value_xi = get_qubit_value(xi, qubits_to_fix)
        value_xj = get_qubit_value(xj, qubits_to_fix)

        if value_xi == 1 and value_xj == 1:
            carry = get_qubit_name()
            qubits_to_fix[carry] = 1

            linear_carry, offset_carry = get_model_single_var(qubits_to_fix[carry])
            bqm.add_variable(carry, linear_carry)
            bqm.offset += offset_carry

            result = xk
        elif value_xi != value_xj:
            carry = xk
            result = get_qubit_name()
            model, _ = get_model(Config.NOT, [xk, result])
            bqm.update(model)
            InputPropagationFile.write_rule(R_NOT, result, [xk], qubits_to_fix)
        else:
            carry = get_qubit_name()
            qubits_to_fix[carry] = 0
            linear_carry, offset_carry = get_model_single_var(qubits_to_fix[carry])
            bqm.add_variable(carry, linear_carry)
            bqm.offset += offset_carry

            result = xk
    else:
        # we cannot do constant propagation
        result = get_qubit_name()
        carry = get_qubit_name()

        def get_full_adder():
            linear = {'aux0': 4.0, carry: 4.0, input1: 2.0, input2: 2.0, input3: 2.0, result: 2.0}
            quadratic = {(carry, 'aux0'): 0.0,
                         (input1, 'aux0'): -4.0,
                         (input1, carry): -4.0,
                         (input2, 'aux0'): -4.0,
                         (input2, carry): -4.0,
                         (input2, input1): 4.0,
                         (input3, 'aux0'): 4.0,
                         (input3, carry): -4.0,
                         (input3, input1): 0.0,
                         (input3, input2): 0.0,
                         (result, 'aux0'): -4.0,
                         (result, carry): 4.0,
                         (result, input1): 0.0,
                         (result, input2): 0.0,
                         (result, input3): -4.0}
            return dimod.BinaryQuadraticModel(linear, quadratic, dimod.BINARY)

        temp_bqm = get_full_adder()
        aux0 = get_qubit_name()
        temp_bqm.relabel_variables({'aux0': aux0})
        InputPropagationFile.write_rule(AUX_FULL_ADDER, aux0, [input1, input2, input3], qubits_to_fix)
        InputPropagationFile.write_rule(CARRY_FULL_ADDER, carry, [input1, input2, input3], qubits_to_fix)
        InputPropagationFile.write_rule(RESULT_FULL_ADDER, result, [input1, input2, input3], qubits_to_fix)
        bqm.update(temp_bqm)
    return carry, result


def optimized_bitwise_add(bitset1: List[int], bitset2: List[int], current_n: int, bqm: dimod.BinaryQuadraticModel,
                          qubits_to_fix: Dict[int, int], fix_last_carry: bool = False) -> QWord:
    result_qword = QWord(len(bitset1))
    result_qubits = []

    current_bit = 0
    carry = -1

    while current_bit < len(bitset1):
        if current_bit == 0:
            carry, result_qubit = optimized_half_adder(bitset1[0], bitset2[0], bqm, qubits_to_fix)
        else:
            current_carry, result_qubit = optimized_full_adder(bitset1[current_bit], bitset2[current_bit], carry, bqm,
                                                               qubits_to_fix)
            carry = current_carry
        current_bit += 1
        result_qubits.append(result_qubit)

    if fix_last_carry:
        qubits_to_fix[carry] = 0
        linear_carry, offset_carry = get_model_single_var(0)
        bqm.add_variable(carry, linear_carry)
        bqm.offset += offset_carry

    result_qword.append_state(result_qubits, current_n)

    return result_qword

def optimized_multiplication(bitset1: List[int], bitset2: List[int], current_n: int, bqm: dimod.BinaryQuadraticModel,
                             qubits_to_fix: Dict[int, int], fix_last_qubit: bool=False):
    assert len(bitset1) == len(bitset2)

    def multiply_by_digit(bitset1, qubit_name, shift):
        temp_result = []
        for i in range(0, shift):
            name_result = get_qubit_name()
            temp_result.append(name_result)
            qubits_to_fix[name_result] = 0

            linear, offset = get_model_single_var(0)
            bqm.add_variable(name_result, linear)
            bqm.offset += offset

        value_operand2 = get_qubit_value(qubit_name, qubits_to_fix)
        for bit in bitset1:
            value_bit = get_qubit_value(bit, qubits_to_fix)
            if value_bit is not None and value_operand2 is not None:
                result_name = get_qubit_name()
                qubits_to_fix[result_name] = value_bit and value_operand2

                linear, offset = get_model_single_var(qubits_to_fix[result_name])
                bqm.add_variable(result_name, linear)
                bqm.offset += offset

                temp_result.append(result_name)
            elif value_bit == 0 or value_operand2 == 0:
                result_name = get_qubit_name()
                qubits_to_fix[result_name] = 0

                linear, offset = get_model_single_var(qubits_to_fix[result_name])
                bqm.add_variable(result_name, linear)
                bqm.offset += offset

                temp_result.append(result_name)
            else:
                result_name = get_qubit_name()
                model, _ = get_model(Config.AND, [bit, qubit_name, result_name])
                bqm.update(model)
                InputPropagationFile.write_rule(R_AND, result_name, [bit, qubit_name], qubits_to_fix)
                temp_result.append(result_name)
        return temp_result

    def add_front_zeros_padding(bits, total_size):
        while len(bits) < total_size:
            name = get_qubit_name()
            bqm.add_variable(name)
            qubits_to_fix[name] = 0
            linear, offset = get_model_single_var(qubits_to_fix[name])
            bqm.add_variable(name, linear)
            bqm.offset += offset
            bits.append(name)
        return bits

    to_sum_words = []

    expected_max_size = 2*len(bitset1)-1
    for i in range(len(bitset2)):
        temp_res = multiply_by_digit(bitset1, bitset2[i], i)
        to_sum_words.append(add_front_zeros_padding(temp_res, expected_max_size))

    result_bitset = optimized_bitwise_add(to_sum_words[0], to_sum_words[1], current_n, bqm, qubits_to_fix)[current_n]

    for i in range(2, len(to_sum_words)):
        result_bitset = optimized_bitwise_add(result_bitset, to_sum_words[i], current_n, bqm, qubits_to_fix)[current_n]

    qword_result = QWord(len(bitset1))
    qword_result.append_state(result_bitset[:len(bitset1)], current_n)
    return qword_result

def optimized_divide(dividend: List[int], divisor: List[int], current_n: int, bqm: dimod.BinaryQuadraticModel,
                     qubits_to_fix:Dict[int, int]) ->  (QWord, QWord):
    assert len(dividend) == len(divisor)

    word_size = len(dividend)
    qword_quotient = QWord(word_size)
    qword_quotient.create_state(bqm, current_n)

    merged_inputs = []
    for e in dividend:
        merged_inputs.append(e)
    for e in divisor:
        merged_inputs.append(e)
    InputPropagationFile.write_rule(QUOTIENT, qword_quotient[current_n], merged_inputs, qubits_to_fix)

    multiplication_qword = optimized_multiplication(divisor, qword_quotient[current_n], current_n, bqm, qubits_to_fix)

    qword_remainder = QWord(word_size)
    qword_remainder.create_state(bqm, current_n)
    InputPropagationFile.write_rule(REMAINDER, qword_remainder[current_n], merged_inputs, qubits_to_fix)

    sum_qword = optimized_bitwise_add(multiplication_qword[current_n], qword_remainder[current_n], current_n, bqm,
                                      qubits_to_fix, True) # fix the last carry to be equal to 0

    is_equal_qword = optimized_is_equal(dividend, sum_qword[current_n], current_n, bqm, qubits_to_fix)

    assert len(is_equal_qword[current_n]) == 1
    is_equal_qubit = is_equal_qword[current_n][0]
    assert isinstance(is_equal_qubit, int)
    # qubits_to_fix[is_equal_qubit] = 1

    # now add the constraint that the remainder cannot be greater than or equal to divisor
    is_less_than_qword = optimized_unsigned_less_than(qword_remainder[current_n], divisor, current_n, bqm,
                                                      qubits_to_fix)
    assert len(is_less_than_qword[current_n]) == 1
    is_less_qubit = is_less_than_qword[current_n][0]
    assert isinstance(is_less_qubit, int)
    # qubits_to_fix[is_less_qubit] = 1

    good_division_const_result = GlobalIndexer.get_name_index()
    decision_variables = [is_equal_qubit, is_less_qubit, good_division_const_result]
    model, _ = get_model(Config.AND, decision_variables)
    bqm.update(model)

    # if remainder is not less than the divisor, then the divisor must be 0
    qubitset_zero = QWord(len(divisor))
    qubitset_zero.create_state(bqm, current_n)
    for qubit in qubitset_zero[current_n]:
        qubits_to_fix[qubit] = 0
    is_divisor_0_qword = optimized_is_equal(divisor, qubitset_zero[current_n], current_n, bqm, qubits_to_fix)
    assert(len(is_divisor_0_qword) == 1)
    is_divisor_0_qubit = is_divisor_0_qword[current_n][0]
    assert isinstance(is_divisor_0_qubit, int)

    result_or = GlobalIndexer.get_name_index()
    decision_variables = [good_division_const_result, is_divisor_0_qubit, result_or]
    model, _ = get_model(Config.OR, decision_variables)
    bqm.update(model)
    qubits_to_fix[result_or] = 1

    return qword_quotient, qword_remainder

def optimized_get_quotient(dividend: List[int], divisor: List[int], current_n: int, bqm: dimod.BinaryQuadraticModel,
                           qubits_to_fix: Dict[int, int]) -> QWord:
    result = optimized_divide(dividend, divisor, current_n, bqm, qubits_to_fix)
    return result[0]

def optimized_get_remainder(dividend: List[int], divisor: List[int], current_n: int, bqm: dimod.BinaryQuadraticModel,
                            qubits_to_fix:Dict[int, int]) -> QWord:
    result = optimized_divide(dividend, divisor, current_n, bqm, qubits_to_fix)
    return result[1]


def create_constant_qubit_value(number: int, size_in_bits: int, bqm: dimod.BinaryQuadraticModel,
                                qubits_to_fix: Dict[int, int]) -> QWord:
    bits = get_bit_repr_of_number(number)

    result_qword = QWord(size_in_bits)
    result_qword.name = "constant_qubit"
    result_qword.create_state(bqm, 0)

    for (bit, name) in zip(bits, result_qword[0]):
        qubits_to_fix[name] = bit

        linear, offset = get_model_single_var(qubits_to_fix[name])
        bqm.add_variable(name, linear)
        bqm.offset += offset
    return result_qword


def optimized_xnor(bitset1: List[int], bitset2: List[int], bqm: dimod.BinaryQuadraticModel,
                   qubits_to_fix: Dict[int, int], current_n = None) -> List[int]:
    assert len(bitset1) == len(bitset2)
    result = []
    for (bit1, bit2) in zip(bitset1, bitset2):

        value_x1 = get_qubit_value(bit1, qubits_to_fix)
        value_x2 = get_qubit_value(bit2, qubits_to_fix)
        # build circuit
        if bit1 == bit2:
            name_result = get_qubit_name()
            qubits_to_fix[name_result] = 1
            result.append(name_result)

            linear, offset = get_model_single_var(1)
            bqm.add_variable(name_result, linear)
            bqm.offset += offset
        elif value_x1 is not None and value_x2 is not None:
            name_result = get_qubit_name()
            qubits_to_fix[name_result] = value_x1 == value_x2

            linear, offset = get_model_single_var(qubits_to_fix[name_result])
            bqm.add_variable(name_result, linear)
            bqm.offset += offset

            result.append(name_result)
        elif (value_x1 is not None and value_x2 is None) or (value_x1 is None and value_x2 is not None):

            if value_x1 is None:
                name_none = bit1
                target_value = value_x2
            else:
                name_none = bit2
                target_value = value_x1

            if target_value == 0:
                name_result = get_qubit_name()
                model, _ = get_model(Config.NOT, [name_none, name_result])
                InputPropagationFile.write_rule(R_NOT, name_result, [name_none], qubits_to_fix)
                bqm.update(model)
                result.append(name_result)
            else:
                result.append(name_none)
        else:
            # intermediary qubits
            nx1 = get_qubit_name()
            nx2 = get_qubit_name()
            nand1 = get_qubit_name()
            nand2 = get_qubit_name()
            name_result = get_qubit_name()
            var_names = {
                'x1': bit1,
                'x2': bit2,
                'nx1': nx1,
                'nx2': nx2,
                'nand1': nand1,
                'nand2': nand2,
                'z': name_result
            }

            model = get_XNOR(var_names)
            bqm.update(model)
            InputPropagationFile.write_rule(R_NOT, nx1, [bit1], qubits_to_fix)
            InputPropagationFile.write_rule(R_NOT, nx2, [bit2], qubits_to_fix)
            InputPropagationFile.write_rule(NAND, nand1, [bit1, bit2], qubits_to_fix)
            InputPropagationFile.write_rule(NAND, nand2, [nx1, nx2], qubits_to_fix)
            InputPropagationFile.write_rule(XNOR, name_result, [bit1, bit2], qubits_to_fix)
            result.append(name_result)

    assert len(result) == len(bitset1)
    return result

def optimized_xor(bitset1: List[int], bitset2: List[int], bqm: dimod.BinaryQuadraticModel,
                  qubits_to_fix: Dict[int, int]) -> List[int]:
    assert len(bitset1) == len(bitset2)
    result = []

    for (bit1, bit2) in zip(bitset1, bitset2):
        value_x1 = get_qubit_value(bit1, qubits_to_fix)
        value_x2 = get_qubit_value(bit2, qubits_to_fix)

        if bit1 == bit2:
            name_result = get_qubit_name()
            qubits_to_fix[name_result] = 0
            result.append(name_result)

            linear, offset = get_model_single_var(0)
            bqm.offset += offset
            bqm.add_variable(name_result, linear)

        elif value_x1 is not None and value_x2 is not None:
            name_result = get_qubit_name()
            qubits_to_fix[name_result] = value_x1 != value_x2
            result.append(name_result)

            linear, offset = get_model_single_var(value_x1 != value_x2)
            bqm.offset += offset
            bqm.add_variable(name_result, linear)
        elif (value_x1 is not None and value_x2 is None) or (value_x1 is None and value_x2 is not None):
            if value_x1 is None:
                name_none = bit1
                target_value = value_x2
            else:
                name_none = bit2
                target_value = value_x1
            if target_value == 1:
                name_result = get_qubit_name()
                model, _ = get_model(Config.NOT, [name_none, name_result])
                InputPropagationFile.write_rule(R_NOT, name_result, [name_none], qubits_to_fix)
                bqm.update(model)
                result.append(name_result)
            else:
                result.append(name_none)
        else:
            # intermediary qubits
            nx1 = get_qubit_name()
            nx2 = get_qubit_name()
            nand1 = get_qubit_name()
            nand2 = get_qubit_name()
            name_result = get_qubit_name()
            var_names = {
                'x1': bit1,
                'x2': bit2,
                'nx1': nx1,
                'nx2': nx2,
                'nand1': nand1,
                'nand2': nand2,
                'z': name_result
            }

            model = get_XOR(var_names)
            if value_x1 is not None and value_x2 is not None:
                raise Exception("not expected constants in XOR")
                # qubits_to_fix[nx1] = not value_x1
                # qubits_to_fix[nx2] = not value_x2
                # qubits_to_fix[nand1] = not (value_x1 and value_x2)
                # qubits_to_fix[nand2] = not ((not value_x1) and (not value_x2))
                # qubits_to_fix[name_result] = value_x1 != value_x2
            bqm.update(model)
            InputPropagationFile.write_rule(R_NOT, nx1, [bit1], qubits_to_fix)
            InputPropagationFile.write_rule(R_NOT, nx2, [bit2], qubits_to_fix)
            InputPropagationFile.write_rule(NAND, nand1, [bit1, bit2], qubits_to_fix)
            InputPropagationFile.write_rule(NAND, nand2, [nx1, nx2], qubits_to_fix)
            InputPropagationFile.write_rule(XOR, name_result, [bit1, bit2], qubits_to_fix)
            result.append(name_result)
    assert len(result) == len(bitset1)
    return result


def optimized_bits_and(_bits: List[int], bqm: dimod.BinaryQuadraticModel, current_n: int,
                       qubits_to_fix: Dict[int, int]) -> QWord:
    assert len(_bits) > 1

    const_names, bits = separate_constants(_bits, qubits_to_fix)

    const_value = get_constant_bits_value(const_names, qubits_to_fix, AND)
    if const_value is not None:
        result_name = GlobalIndexer.get_name_index()
        qubits_to_fix[result_name] = const_value

        linear, offset = get_model_single_var(const_value)
        bqm.offset += offset
        bqm.add_variable(result_name, linear)

        qword_result = QWord(1)
        qword_result.append_state([result_name], current_n)
        return qword_result

    if len(bits) == 0:
        # all values are 1
        result_name = GlobalIndexer.get_name_index()
        qubits_to_fix[result_name] = 1

        linear, offset = get_model_single_var(1)
        bqm.offset += offset
        bqm.add_variable(result_name, linear)

        qword_result = QWord(1)
        qword_result.append_state([result_name], current_n)
        return qword_result
    elif len(bits) == 1:
        qword_result = QWord(1)
        qword_result.append_state([bits[0]], current_n)
        return qword_result

    intermediate_result = GlobalIndexer.get_name_index()
    decision_variables = [bits[0], bits[1], intermediate_result]
    model, _ = get_model(Config.AND, decision_variables)
    InputPropagationFile.write_rule(R_AND, intermediate_result, [bits[0], bits[1]], qubits_to_fix)
    bqm.update(model)

    for bit in bits[2:]:
        prev_intermediate = intermediate_result
        intermediate_result = get_qubit_name()
        decision_variables = [bit, prev_intermediate, intermediate_result]
        model, _ = get_model(Config.AND, decision_variables)
        InputPropagationFile.write_rule(R_AND, intermediate_result, [bit, prev_intermediate], qubits_to_fix)
        bqm.update(model)

    qword_result = QWord(1)
    qword_result.append_state([intermediate_result], current_n)
    return qword_result


def optimized_is_equal(bitset1: List[int], bitset2: List[int], current_n: int, bqm: dimod.BinaryQuadraticModel,
                       qubits_to_fix: Dict[int, int]) -> QWord:
    xnor_result = optimized_xnor(bitset1, bitset2, bqm, qubits_to_fix, current_n)
    return optimized_bits_and(xnor_result, bqm, current_n, qubits_to_fix)


def optimized_bitwise_or(bitset1: List[int], bitset2: List[int], current_n: int, bqm: dimod.BinaryQuadraticModel,
                         qubits_to_fix: Dict[int, int]) -> QWord:
    assert len(bitset1) == len(bitset2)
    result_bits = []

    for (bit1, bit2) in zip(bitset1, bitset2):
        is_bit1_constant = bit1 in qubits_to_fix.keys()
        is_bit2_constant = bit2 in qubits_to_fix.keys()
        if is_bit1_constant and is_bit2_constant:
            name_bit_result = get_qubit_name()
            qubits_to_fix[name_bit_result] = qubits_to_fix[bit1] or qubits_to_fix[bit2]

            linear, offset = get_model_single_var(qubits_to_fix[name_bit_result])
            bqm.offset += offset
            bqm.add_variable(name_bit_result, linear)

            result_bits.append(name_bit_result)
            InputPropagationFile.write_rule(OR, name_bit_result, [bit1, bit2], qubits_to_fix)

        elif is_bit1_constant:
            if qubits_to_fix[bit1] == 1:
                result_bits.append(bit1)
            else:
                result_bits.append(bit2)
        elif is_bit2_constant:
            if qubits_to_fix[bit2] == 1:
                result_bits.append(bit2)
            else:
                result_bits.append(bit1)
        else:
            if bit1 == bit2:
                result_bits.append(bit1)
            else:
                name_bit_result = get_qubit_name()
                model, _ = get_model(Config.OR, [bit1, bit2, name_bit_result])
                bqm.update(model)
                result_bits.append(name_bit_result)
                InputPropagationFile.write_rule(OR, name_bit_result, [bit1, bit2], qubits_to_fix)

    assert len(result_bits) == len(bitset1)
    result_qword = QWord(len(bitset1))
    result_qword.append_state(result_bits, current_n)
    return result_qword


def optimized_bits_or(bits: List[int], bqm: dimod.BinaryQuadraticModel, qubits_to_fix: Dict[int, int]) -> int:

    if len(bits) == 1:
        return bits[0]

    const_names, bits = separate_constants(bits, qubits_to_fix)

    const_value = get_constant_bits_value(const_names, qubits_to_fix, OR)
    if const_value is not None:
        result_name = GlobalIndexer.get_name_index()
        linear_coeff, add_offset = get_model_single_var(const_value)
        bqm.add_variable(result_name, linear_coeff)
        bqm.offset += add_offset
        qubits_to_fix[result_name] = const_value
        return result_name

    if len(bits) == 0:
        # all values are 0
        result_name = GlobalIndexer.get_name_index()
        linear_coeff, add_offset = get_model_single_var(0)
        bqm.add_variable(result_name, linear_coeff)
        bqm.offset += add_offset
        qubits_to_fix[result_name] = 0
        return result_name
    elif len(bits) == 1:
        or_result = GlobalIndexer.get_name_index()
        temp_qubit = GlobalIndexer.get_name_index()
        qubits_to_fix[temp_qubit] = 0
        decision_variables = [temp_qubit, bits[0], or_result]
        model, _ = get_model(Config.OR, decision_variables)
        InputPropagationFile.write_rule(OR, or_result, [temp_qubit, bits[0]], qubits_to_fix)
        bqm.update(model)
        return or_result

    intermediate_result = GlobalIndexer.get_name_index()
    decision_variables = [bits[0], bits[1], intermediate_result]
    model, _ = get_model(Config.OR, decision_variables)
    InputPropagationFile.write_rule(OR, intermediate_result, [bits[0], bits[1]], qubits_to_fix)
    bqm.update(model)

    for bit in bits[2:]:
        prev_intermediate = intermediate_result
        intermediate_result = get_qubit_name()
        decision_variables = [bit, prev_intermediate, intermediate_result]
        model, _ = get_model(Config.OR, decision_variables)
        bqm.update(model)
        InputPropagationFile.write_rule(OR, intermediate_result, [bit, prev_intermediate], qubits_to_fix)
    return intermediate_result
