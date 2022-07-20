from qword_tools import *
import json


class InputChecker:
    qubits_to_fix: Dict[int, int] = {}
    linear = {}
    quadratic = {}
    quadratic2 = {}
    offset = 0

    def __init__(self):
        self.qubits_to_fix = {}
        self.linear = {}
        self.quadratic = {}
        self.offset = 0

    @staticmethod
    def get_rule_value(rule, inputs):
        if rule == NAND:
            assert len(inputs) == 2
            value1 = get_qubit_value(inputs[0], InputChecker.qubits_to_fix)
            value2 = get_qubit_value(inputs[1], InputChecker.qubits_to_fix)
            if value1 is None or value2 is None:
                return None

            return not (value1 and value2)
        elif rule == R_AND:
            assert len(inputs) == 2
            value1 = get_qubit_value(inputs[0], InputChecker.qubits_to_fix)
            value2 = get_qubit_value(inputs[1], InputChecker.qubits_to_fix)
            if value1 is None or value2 is None:
                return None

            return value1 and value2
        elif rule == OR:
            assert len(inputs) == 2
            value1 = get_qubit_value(inputs[0], InputChecker.qubits_to_fix)
            value2 = get_qubit_value(inputs[1], InputChecker.qubits_to_fix)
            if value1 is None or value2 is None:
                return None
            return value1 or value2
        elif rule == XNOR:
            assert len(inputs) == 2
            value1 = get_qubit_value(inputs[0], InputChecker.qubits_to_fix)
            value2 = get_qubit_value(inputs[1], InputChecker.qubits_to_fix)
            if value1 is None or value2 is None:
                return None
            return value1 == value2
        elif rule == XOR:
            assert len(inputs) == 2
            value1 = get_qubit_value(inputs[0], InputChecker.qubits_to_fix)
            value2 = get_qubit_value(inputs[1], InputChecker.qubits_to_fix)
            if value1 is None or value2 is None:
                return None
            return value1 != value2
        elif rule == AUX_HALF_ADDER:
            assert len(inputs) == 2
            value1 = get_qubit_value(inputs[0], InputChecker.qubits_to_fix)
            value2 = get_qubit_value(inputs[1], InputChecker.qubits_to_fix)
            if value1 is None or value2 is None:
                return None
            return value1 and (not value2)
        elif rule == AUX_FULL_ADDER:
            assert len(inputs) == 3
            value_input1 = get_qubit_value(inputs[0], InputChecker.qubits_to_fix)
            value_input2 = get_qubit_value(inputs[1], InputChecker.qubits_to_fix)
            value_input3 = get_qubit_value(inputs[2], InputChecker.qubits_to_fix)
            if value_input1 is None or value_input2 is None or value_input3 is None:
                return None

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
            assert len(inputs) == 1

            value1 = get_qubit_value(inputs[0], InputChecker.qubits_to_fix)

            if value1 is None:
                return None

            return not value1
        elif rule == CARRY_HALF_ADDER:
            return InputChecker.get_rule_value(R_AND, inputs)
        elif rule == CARRY_FULL_ADDER:
            assert len(inputs) == 3

            value_input1 = get_qubit_value(inputs[0], InputChecker.qubits_to_fix)
            value_input2 = get_qubit_value(inputs[1], InputChecker.qubits_to_fix)
            value_input3 = get_qubit_value(inputs[2], InputChecker.qubits_to_fix)

            if value_input1 is None or value_input2 is None or value_input3 is None:
                return None

            return (value_input1 + value_input2 + value_input3) > 1
        elif rule == RESULT_HALF_ADDER:
            assert len(inputs) == 2

            value_input1 = get_qubit_value(inputs[0], InputChecker.qubits_to_fix)
            value_input2 = get_qubit_value(inputs[1], InputChecker.qubits_to_fix)

            if value_input1 is None or value_input2 is None:
                return None
            return (value_input1 + value_input2) % 2
        elif rule == RESULT_FULL_ADDER:
            assert len(inputs) == 3

            value_input1 = get_qubit_value(inputs[0], InputChecker.qubits_to_fix)
            value_input2 = get_qubit_value(inputs[1], InputChecker.qubits_to_fix)
            value_input3 = get_qubit_value(inputs[2], InputChecker.qubits_to_fix)

            if value_input1 is None or value_input2 is None or value_input3 is None:
                return None
            return (value_input1 + value_input2 + value_input3) % 2
        elif rule == MATRIARCH1:
            assert len(inputs) == 2

            value1 = get_qubit_value(inputs[0], InputChecker.qubits_to_fix)
            value2 = get_qubit_value(inputs[1], InputChecker.qubits_to_fix)

            if value1 is None or value2 is None:
                return None

            return (not value1) and value2
        else:
            raise Exception(f"UNKNOWN RULE: {rule}")

    @staticmethod
    def get_rules_from_file(filename):
        file = open(filename, 'r')
        rules = {}
        for line in file.readlines():
            temp = line.split()

            rule = temp[0]
            if rule == QUOTIENT or rule == REMAINDER:
                value = {'rule': rule}
                qubits = [int(x) for x in temp[1:]]
                assert(len(qubits) % 3 == 0) # we have 3 bitvectors

                bitvector_size = len(qubits)//3
                dividend = []
                divisor = []
                for i in range(bitvector_size):
                    dividend.append(qubits[bitvector_size + i])
                    divisor.append(qubits[bitvector_size*2 + i])

                assert(len(dividend) == len(divisor))
                value["dividend"] = dividend
                value["divisor"] = divisor
                for i in range(bitvector_size):
                    value['index'] = i
                    rules[qubits[i]] = value
            else:
                inputs = [int(x) for x in temp[2:]]
                rules[int(temp[1])] = {'rule': rule, 'inputs': inputs}
        file.close()
        return rules

    @staticmethod
    def solve_dependency(name, rules):
        if not (name in InputChecker.qubits_to_fix):
            if name in rules.keys():
                if rules[name]['rule'] == QUOTIENT or rules[name]['rule'] == REMAINDER:
                    dividend = []
                    divisor = []
                    for (dependecy1, dependency2) in zip(rules[name]['dividend'], rules[name]['divisor']):
                        InputChecker.solve_dependency(dependecy1, rules)
                        InputChecker.solve_dependency(dependency2, rules)

                        val = get_qubit_value(dependecy1, InputChecker.qubits_to_fix)
                        assert(val is not None)
                        dividend.append(int(val))

                        val = get_qubit_value(dependency2, InputChecker.qubits_to_fix)
                        assert(val is not None)
                        divisor.append(int(val))
                    dec_divisor = get_decimal_representation(divisor)
                    dec_dividend = get_decimal_representation(dividend)
                    if dec_divisor == 0:

                        InputChecker.qubits_to_fix[name] = 0
                    else:
                        if  rules[name]['rule'] == QUOTIENT:
                            dec_result = dec_dividend // dec_divisor
                        else:
                            assert(rules[name]['rule'] == REMAINDER)
                            dec_result = dec_dividend % dec_divisor
                        assert(len(rules[name]['divisor']) == len(rules[name]['dividend']))
                        bin_result = get_bit_repr_of_number(dec_result, len(rules[name]['divisor']))
                        InputChecker.qubits_to_fix[name] = bin_result[rules[name]['index']]
                else:
                    for input_ in rules[name]['inputs']:
                        InputChecker.solve_dependency(input_, rules)
                    value = InputChecker.get_rule_value(rules[name]['rule'], rules[name]['inputs'])

                    InputChecker.qubits_to_fix[name] = value
            else:
                InputChecker.qubits_to_fix[name] = 0

    @staticmethod
    def run_input(input_: Dict[int, int], qubits_to_fix: Dict[int, int], rules_file: str):
        qubits_to_fix = {int(k): v for (k, v) in qubits_to_fix.items()}
        # print("initial offset:", InputChecker.offset)
        rules = InputChecker.get_rules_from_file(rules_file)

        InputChecker.qubits_to_fix = qubits_to_fix
        keys_to_fix = rules.keys()

        for (qubit_name, value) in input_.items():
            # bqm.fix_variable(qubit_name, value)
            InputChecker.qubits_to_fix[qubit_name] = value

        for key in keys_to_fix:
            InputChecker.solve_dependency(key, rules)

        # start fixing variables
        for (var, bias) in InputChecker.linear.items():

            if var in InputChecker.qubits_to_fix.keys():
                InputChecker.offset += InputChecker.qubits_to_fix[var] * bias
            # else:
            #     print("WARNING linear without fixed value found.")

        for ((u, v), coupling) in InputChecker.quadratic.items():

            if u in InputChecker.qubits_to_fix.keys():
                u_value = InputChecker.qubits_to_fix[u]
                if v in InputChecker.qubits_to_fix.keys():
                    v_value = InputChecker.qubits_to_fix[v]
                    InputChecker.offset += u_value * v_value * coupling
                # else:
                #     print("WARNING quadratic without fixed value found.")
            # else:
            #     print("WARNING quadratic without fixed value found.")

        # print("offset:", InputChecker.offset)
        return InputChecker.offset

    @staticmethod
    def process_coo(path):
        InputChecker.linear = {}
        InputChecker.quadratic = {}
        with open(path) as coo_file:
            for line in coo_file.readlines():
                temp = line.split()
                temp = [int(temp[0]), int(temp[1]), float(temp[2])]
                assert len(temp) == 3
                if temp[0] == temp[1]:
                    InputChecker.linear[temp[0]] = temp[2]
                else:
                    first_element = min(temp[0], temp[1])
                    second_element = max(temp[0], temp[1])
                    if first_element not in InputChecker.quadratic2:
                        InputChecker.quadratic2[first_element] = {}
                    if second_element not in InputChecker.quadratic2:
                        InputChecker.quadratic2[second_element] = {}
                    InputChecker.quadratic2[first_element][second_element] = temp[2]
                    InputChecker.quadratic2[second_element][first_element] = temp[2]
                    InputChecker.quadratic[(first_element, second_element)] = temp[2]

    @staticmethod
    def run_checker(directory_path: str, input_value: int):
        with open(f"{directory_path}context.json") as json_file:
            context = json.load(json_file)
            with open(f"{directory_path}qubits_to_fix.json") as fixed_qubits_file:
                qubits_to_fix = json.load(fixed_qubits_file)

                # keys are strings
                qubits_to_fix = {int(k): v for (k, v) in qubits_to_fix.items()}

                InputChecker.process_coo(f"{directory_path}adj.coo")
                InputChecker.offset = context['offset']

                input_vectors = context['input']
                if len(input_vectors) > 0:
                    input_values = get_bit_repr_of_number(input_value, len(input_vectors[0]))
                    input_mapping = {}

                    for input_names in input_vectors:
                        for (name, val) in zip(input_names, input_values):
                            input_mapping[name] = val
                else:
                    input_mapping = {}
                bias = InputChecker.run_input(input_mapping, qubits_to_fix,
                                              f"{directory_path}input_propagation.unicorn")
                bad_states_to_line_no = {int(k): v for (k, v) in context['bad_states_to_line_no'].items()}
                bad_states = []
                for bad in context['bad_states']:
                    if InputChecker.qubits_to_fix[bad] == 1:
                        bad_states.append(bad_states_to_line_no[bad])

                return bias, bad_states
