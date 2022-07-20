from typing import Set

from dimod import BinaryQuadraticModel
from qword_tools import *
from bqm_input_checker import InputChecker



class Instruction:
    # BEGIN static attributes
    all_instructions: Dict[int, List[str]] = {}  # maps <sid> -> (list of tokens of the instruction)
    current_n = 0
    bqm: BinaryQuadraticModel = BinaryQuadraticModel(BQM_TYPE)
    memory: Optional[QWord] = None
    qubits_to_fix: Dict[int, int] = {}  # maps qubit name to binary value to fix this qubits
    qubits_end_data_segment: Optional[QWord] = None  # last address data segment. It is not valid.
    qubits_end_heap: Optional[QWord] = None  # last address of the heap. It is not valid.
    addresses_qubits: List[List[int]] = []  # qubits that represent the actual addresses (not the slots)
    created_states_ids: Dict[int, QWord] = {}  # current_n -> QWord
    address_to_local_offsets: Dict[int, int] = {}  # maps real address to the word_index it refers to
    initialize_states: bool = True
    bad_states: List[int] = []
    bad_states_to_line_no: Dict[int, int] = {}
    input_nids: List[List[int]] = []
    # model settings
    ADDRESS_WORD_SIZE = 4  # address are described by 32 bit numbers

    ADDRESS_STEP_SIZE = 1

    BEGIN_DATASEGMENT = 0  # end of code segment rounded up to next page, first valid address for data segment
    SIZE_DATASEGMENT = 2  # 2  # data segment will contain SIZE_DATA SEGMENT 64-bit machine words

    BEGIN_HEAP = 2  # first valid address for heap
    SIZE_HEAP = 1  # heap will contain SIZE_HEAP 64-bit machine words

    # for our running example we only care on the 12 address
    BEGIN_STACK = 12  # highest address in memory (not valid cause it grows downwards)
    SIZE_STACK = 9  # stack will contain SIZE_STACK 64-bit machine words

    WORD_SIZE = 64

    output_dir = "input_checker_files_slice/"
    counter = 0

    # END static attributes

    @staticmethod
    def set_setting(setting):
        print("output dir: ", Instruction.output_dir)
        Instruction.ADDRESS_WORD_SIZE = setting['address_word_size']
        Instruction.ADDRESS_STEP_SIZE = setting['address_step_size']
        Instruction.BEGIN_DATASEGMENT = setting['begin_datasegment']
        Instruction.SIZE_DATASEGMENT = setting['size_datasegment']
        Instruction.BEGIN_HEAP = setting['begin_heap']
        Instruction.SIZE_HEAP = setting['size_heap']
        Instruction.BEGIN_STACK = setting['begin_stack']
        Instruction.SIZE_STACK = setting['size_stack']
        Instruction.WORD_SIZE = setting['word_size']

    def __init__(self, instruction: List[str]):

        self.qubit_prefix = f"{instruction[0]}{instruction[1]}"
        self.instruction = instruction
        self.base_class = None

        if len(instruction) < 2:
            # each instruction has at least 2 elements. Always.
            raise Exception(f'error parsing instruction: {" ".join(instruction)}')
        self.name = instruction[1]
        try:
            self.id = int(instruction[0])
        except IndexError:
            raise Exception(f'error parsing instruction: {" ".join(instruction)}')

        Instruction.initialize_memory_addresses()

    def set_instruction(self):

        if self.name == SORT:
            self.base_class = Sort(self.instruction)
        elif self.name == STATE:
            self.base_class = State(self.instruction)
        elif self.name == CONSTD:
            self.base_class = State(self.instruction)
        elif self.name == ZERO or self.name == ONE:
            self.base_class = State(self.instruction)
        elif self.name == INPUT:
            self.base_class = Input(self.instruction)
        elif self.name == INIT:
            self.base_class = Init(self.instruction)
        elif self.name == NEXT:
            self.base_class = Next(self.instruction)
        elif self.name == ADD or self.name == SUB:
            self.base_class = Add(self.instruction)
        elif self.name == INC or self.name == DEC:
            self.base_class = Add(self.instruction)
        elif self.name == MUL:
            self.base_class = Mul(self.instruction)
        elif self.name == ITE:
            self.base_class = Ite(self.instruction)
        elif self.name == WRITE:
            self.base_class = Write(self.instruction)
        elif self.name == READ:
            self.base_class = Read(self.instruction)
        elif self.name == UEXT:
            self.base_class = Uext(self.instruction)
        elif self.name == AND:
            self.base_class = And(self.instruction)
        elif self.name == NOT:
            self.base_class = Not(self.instruction)
        elif self.name == EQ:
            self.base_class = Eq(self.instruction)
        elif self.name == ULT:
            self.base_class = Ult(self.instruction)
        elif self.name == ULTE:
            self.base_class = Ulte(self.instruction)
        elif self.name == UGT:
            self.base_class = Ugt(self.instruction)
        elif self.name == UGTE:
            self.base_class = Ugte(self.instruction)
        elif self.name == UDIV:
            self.base_class = Udiv(self.instruction)
        elif self.name == UREM:
            self.base_class = Urem(self.instruction)
        elif self.name == BAD:
            self.base_class = Bad(self.instruction)
        elif self.name == NEQ:
            self.base_class = Neq(self.instruction)
        elif self.name == SLICE:
            self.base_class = Slice(self.instruction)
        else:
            raise Exception(f"Not valid instruction: {self}")

    def raise_error(self):
        pass
        # this function is for debugging purposes
        # if self.name not in [STATE, INPUT, SORT, CONSTD]:
        #     bias = self.evaluate_bqm()
        #     if bias > 0:
        #         raise Exception(self.id, self.name, self.current_n)


    def get_last_qubitset(self, name: str, qword: QWord) -> List[int]:
        if name in [STATE, INPUT]:
            if self.current_n - 1 in qword.states.keys():
                return qword[self.current_n - 1]
            else:
                # assert not (self.current_n in qword.states.keys())
                return qword.top

        if name in [CONSTD, ONE, ZERO]:
            return qword[0]

        if name in [NEXT, SORT, INIT]:
            raise Exception(f"Cannot determine prev. state for instruction {self.instruction}")

        return qword[self.current_n]

    def get_instruction_at_index(self, index: int) -> List[str]:
        return self.all_instructions[abs(int(self.instruction[index]))]

    @property
    def specific_subclass(self) -> object:
        if self.base_class is None:
            self.set_instruction()
        return self.base_class

    def get_sort(self):
        return Sort(self.all_instructions[int(self.instruction[2])])

    def execute(self) -> Optional[QWord]:
        if self.name in [NEXT, SORT, INIT]:
            result = self.specific_subclass.execute()
            self.raise_error()
            return result

        if isinstance(self.specific_subclass, State):
            result = self.specific_subclass.execute()
            self.raise_error()
            return result

        if self.id in Instruction.created_states_ids.keys():
            if self.name in [CONSTD, ONE, ZERO]:
                # for these values we only access timestep 0. If the id-key exists then dont worry processing.
                self.specific_subclass.execute()
                result = Instruction.created_states_ids[self.id]
                self.raise_error()
                return result

            if self.current_n in Instruction.created_states_ids[self.id].states.keys():
                pass
            else:
                result_qword = self.specific_subclass.execute()
                self.raise_error()
                # assert len(result_qword.states) == 1
                state = result_qword.top
                Instruction.created_states_ids[self.id].append_state(state, Instruction.current_n)
        else:
            result_qword = self.specific_subclass.execute()
            self.raise_error()
            assert len(result_qword.states) == 1
            Instruction.created_states_ids[self.id] = result_qword

        return Instruction.created_states_ids[self.id]

    @staticmethod
    def clean_bqm():
        Instruction.bqm = BinaryQuadraticModel.empty(BQM_TYPE)

    @staticmethod
    def initialize_memory_addresses():
        """
        creates qubits to represent the numeric values of addresses
        :return:
        """

        if len(Instruction.addresses_qubits) == 0:
            # only create qubits if addresses has not been initialized before.
            local_offset = 0
            # create addresses for data segment
            for address_index in range(Instruction.SIZE_DATASEGMENT):
                address = Instruction.BEGIN_DATASEGMENT + Instruction.ADDRESS_STEP_SIZE * address_index
                Instruction.addresses_qubits.append(
                    create_constant_qubit_value(address, Instruction.ADDRESS_WORD_SIZE, Instruction.bqm,
                                                Instruction.qubits_to_fix)[0])
                Instruction.address_to_local_offsets[address] = local_offset
                local_offset += 1

            # create addresses for heap
            for address_index in range(Instruction.SIZE_HEAP):
                address = Instruction.BEGIN_HEAP + Instruction.ADDRESS_STEP_SIZE * address_index
                Instruction.addresses_qubits.append(
                    create_constant_qubit_value(address, Instruction.ADDRESS_WORD_SIZE, Instruction.bqm,
                                                Instruction.qubits_to_fix)[0])
                Instruction.address_to_local_offsets[address] = local_offset
                local_offset += 1

            # create_addresses for stack
            for address_index in range(Instruction.SIZE_STACK):
                # consider that stack grows downwards
                address = Instruction.BEGIN_STACK - Instruction.ADDRESS_STEP_SIZE * (address_index + 1)
                Instruction.addresses_qubits.append(
                    create_constant_qubit_value(address, Instruction.ADDRESS_WORD_SIZE, Instruction.bqm,
                                                Instruction.qubits_to_fix)[0])

                Instruction.address_to_local_offsets[address] = local_offset
                local_offset += 1

    @staticmethod
    def fix_qubits():
        offset = Instruction.bqm.offset
        linear_variables = {}
        quadratic_variables = {}

        for (var, bias) in Instruction.bqm.linear.items():
            if var in Instruction.qubits_to_fix.keys():
                offset += Instruction.qubits_to_fix[var] * bias
            else:
                linear_variables[var] = bias

        for ((u, v), coupling) in Instruction.bqm.quadratic.items():
            if u in Instruction.qubits_to_fix.keys():
                u_value = Instruction.qubits_to_fix[u]
                if v in Instruction.qubits_to_fix.keys():
                    v_value = Instruction.qubits_to_fix[v]
                    offset += u_value * v_value * coupling
                else:
                    if v in linear_variables.keys():
                        linear_variables[v] += coupling * u_value
                    else:
                        linear_variables[v] = coupling * u_value
            elif v in Instruction.qubits_to_fix.keys():
                v_value = Instruction.qubits_to_fix[v]
                if u in linear_variables.keys():
                    linear_variables[u] += coupling * v_value
                else:
                    linear_variables[u] = coupling * v_value
            else:
                quadratic_variables[(u, v)] = coupling
        Instruction.bqm = dimod.BinaryQuadraticModel(linear_variables, quadratic_variables, dimod.BINARY)
        Instruction.bqm.offset = offset

    @staticmethod
    def evaluate_bqm():
        offset = Instruction.bqm.offset
        linear_variables = {}
        quadratic_variables = {}

        for (var, bias) in Instruction.bqm.linear.items():
            if var in Instruction.qubits_to_fix.keys():
                offset += Instruction.qubits_to_fix[var] * bias
            else:
                linear_variables[var] = bias

        for ((u, v), coupling) in Instruction.bqm.quadratic.items():
            if u in Instruction.qubits_to_fix.keys():
                u_value = Instruction.qubits_to_fix[u]
                if v in Instruction.qubits_to_fix.keys():
                    v_value = Instruction.qubits_to_fix[v]
                    offset += u_value * v_value * coupling
                else:
                    if v in linear_variables.keys():
                        linear_variables[v] += coupling * u_value
                    else:
                        linear_variables[v] = coupling * u_value
            elif v in Instruction.qubits_to_fix.keys():
                v_value = Instruction.qubits_to_fix[v]
                if u in linear_variables.keys():
                    linear_variables[u] += coupling * v_value
                else:
                    linear_variables[u] = coupling * v_value
            else:
                quadratic_variables[(u, v)] = coupling
        return offset

    @staticmethod
    def add_qubits_to_fix_from_bitset(names, values):
        for (name, value) in zip(names, values):
            Instruction.qubits_to_fix[name] = value

    @staticmethod
    def clean_static_variables():
        Instruction.all_instructions = {}
        Instruction.current_n = 0
        Instruction.bqm = BinaryQuadraticModel(BQM_TYPE)
        Instruction.qubits_to_fix = {}
        Instruction.qubits_end_data_segment = None
        Instruction.qubits_end_heap = None
        Instruction.addresses_qubits = []
        Instruction.created_states_ids = {}
        Instruction.address_to_local_offsets = {}
        Instruction.bad_states = []
        Instruction.bad_states_to_line_no = {}
        Instruction.input_nids = []

    @staticmethod
    def is_constant(qubit_names):
        for name in qubit_names:
            if Instruction.qubits_to_fix.get(name) is None:
                return False
        return True

    @staticmethod
    def get_fixed_bin_representation(qubit_names):
        """
        result has LSB at index 0
        :param qubit_names:
        :return:
        """
        result = []
        for name in qubit_names:
            if Instruction.qubits_to_fix.get(name) is None:
                raise Exception("cannot get fixed value cause qubit is not going to be fixed.")
            result.append(Instruction.qubits_to_fix[name])

        return result

    @staticmethod
    def or_bad_states():

        result = optimized_bits_or(Instruction.bad_states, Instruction.bqm, Instruction.qubits_to_fix)
        Instruction.qubits_to_fix[result] = 1  # make any bad state happen
        return result  # returns the qubit name

    @staticmethod
    def get_variables_count():
        return len(Instruction.bqm.linear.keys()) - len(Instruction.qubits_to_fix.keys())


class Init(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self):
        operand1 = Instruction(self.get_instruction_at_index(3))
        qword1 = operand1.execute()
        qubit_set1 = qword1[0]

        operand2 = Instruction(self.get_instruction_at_index(4))
        qword2 = operand2.execute()
        qubit_set2 = self.get_last_qubitset(operand2.name, qword2)

        for (index, qubit_name) in enumerate(qubit_set2):
            Instruction.qubits_to_fix[qubit_set1[index]] = Instruction.qubits_to_fix[qubit_name]

        qword1.append_state(qubit_set2, 1)
        return qword1


class Input(Instruction):

    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        sort = self.get_sort().execute()
        if self.id in Instruction.created_states_ids.keys():
            #if already exists a hashmap for this id
            result_qword = Instruction.created_states_ids[self.id]
            #
            # # we need a set of qubits for the current timestep
            if not (Instruction.current_n in Instruction.created_states_ids[self.id].states.keys()):
                result_qword.create_state(Instruction.bqm, Instruction.current_n)
                Instruction.input_nids.append(Instruction.created_states_ids[self.id][Instruction.current_n])
        else:
            # this instruction's id does not exists yet.
            result_qword = QWord(sort.size_in_bits)
            result_qword.name = f"{self.id}_input_{self.current_n}"
            result_qword.create_state(Instruction.bqm, 1)
            Instruction.created_states_ids[self.id] = result_qword
            Instruction.input_nids.append(Instruction.created_states_ids[self.id][1])
        return Instruction.created_states_ids[self.id]  # result_qword


class Sort(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> QWord:
        """
        :return: empty QWord without creating qubits.
        """
        sort_name = self.instruction[2]
        bit_count = int(self.instruction[3])
        if sort_name == "array":
            # arrays are represented as a list of qubits (1 dimension)
            dimension1 = Sort(self.get_instruction_at_index(3)).execute()
            dimension2 = Sort(self.get_instruction_at_index(4)).execute()
            bit_count = (2 ** dimension1.size_in_bits) * dimension2.size_in_bits
        elif sort_name != "bitvec":
            raise Exception(f"not valid instruction: {self}")

        return QWord(bit_count)


class State(Instruction):
    # TODO: Custom names

    def __init__(self, instruction):
        super().__init__(instruction)

    def is_new(self):
        return not (self.id in Instruction.created_states_ids.keys())

    def execute(self) -> QWord:
        if self.is_new():
            # if self.instruction[-1] == "memory" or self.instruction[-1] == "memory-dump":
            #     memory_size = WORD_SIZE * (SIZE_DATASEGMENT + SIZE_HEAP + SIZE_STACK)
            #     qword = QWord(memory_size)
            #     qword.name = self.qubit_prefix
            #     qword.create_state(Instruction.bqm, 0)
            #     Instruction.memory = qword
            #
            #     # adds qubits to represent the addresses we can access during runtime.
            #     Instruction.initialize_memory_addresses()
            #
            #     # returns a vector full of zeros, we use this to initialize memory with zeros
            #     bit_representation = get_bit_repr_of_number(0, qword.size_in_bits)
            # else:
            sort = self.get_sort()
            qword = sort.execute()
            qword.name = self.qubit_prefix
            qword.create_state(self.bqm, 0)

            # returns a vector full of zeros, we use this to initialize memory with zeros
            bit_representation = get_bit_repr_of_number(0, qword.size_in_bits)
            Instruction.created_states_ids[self.id] = qword

            if self.instruction[1] == CONSTD:
                # returns a vector in which index 0 is LSB, and it represent the value of this constant value
                bit_representation = get_bit_repr_of_number(int(self.instruction[3]), qword.size_in_bits)

            if self.instruction[1] == ZERO:
                # returns a vector full of zeros, used to initialize this constant
                bit_representation = get_bit_repr_of_number(0, qword.size_in_bits)

            if self.instruction[1] == ONE:
                # first element of this vector represents a 1. Used to initialize some qubits that represent this value
                bit_representation = get_bit_repr_of_number(1, qword.size_in_bits)

            if Instruction.initialize_states or self.instruction[1] in [CONSTD, ZERO, ONE]:
                # if flag is turn on or we are dealing with constants then we initialize this state/constant
                Instruction.add_qubits_to_fix_from_bitset(qword[0], bit_representation)
        return Instruction.created_states_ids[self.id]


class Next(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        previous_state = Instruction(self.get_instruction_at_index(3)).execute()
        future_state = Instruction(self.get_instruction_at_index(4))
        qword_future = future_state.execute()  # gets bitvector of the 2nd operand
        if previous_state and future_state:
            previous_state.append_state(self.get_last_qubitset(future_state.name, qword_future),
                                        self.current_n)
        else:
            # if for some reason one, evaluating one of the operands returns None we throw an error
            raise Exception(f"not valid transition: {self}")
        return None


# Arithmetic operations
class Add(Instruction):

    # TODO: optimization
    def __init__(self, instruction):
        super(Add, self).__init__(instruction)

    def execute(self) -> Optional[QWord]:
        sort = self.get_sort().execute()
        operand1 = Instruction(self.get_instruction_at_index(3))
        qword1 = operand1.execute()
        qubit_set1 = self.get_last_qubitset(operand1.name, qword1)
        if self.instruction[1] == ADD:
            operand2 = Instruction(self.get_instruction_at_index(4))
            qword2 = operand2.execute()
            qubit_set2 = self.get_last_qubitset(operand2.name, qword2)
        elif self.instruction[1] == SUB:
            operand2 = Instruction(self.get_instruction_at_index(4))
            qword2 = operand2.execute()
            qubitset = self.get_last_qubitset(operand2.name, qword2)
            res_qword = optimized_get_twos_complement(qubitset, Instruction.current_n, Instruction.bqm,
                                                      Instruction.qubits_to_fix)
            qubit_set2 = res_qword[Instruction.current_n]
        else:
            qword2 = QWord(sort.size_in_bits)
            qword2.create_state(Instruction.bqm, Instruction.current_n)
            qubit_set2 = qword2[Instruction.current_n]
            if self.instruction[1] == INC:
                bit_ = get_bit_repr_of_number(1, sort.size_in_bits)
            else:
                # is decrementing by 1
                bit_ = get_bit_repr_of_number(-1, sort.size_in_bits)
            Instruction.add_qubits_to_fix_from_bitset(qubit_set2, bit_)

        assert len(qubit_set1) == len(qubit_set2)
        assert len(qubit_set1) == sort.size_in_bits
        result = optimized_bitwise_add(qubit_set1, qubit_set2, Instruction.current_n, Instruction.bqm,
                                       Instruction.qubits_to_fix)
        return result


class Mul(Instruction):
    # TODO: Optimization
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> QWord:
        # get last timestep
        operand1 = Instruction(self.get_instruction_at_index(3))
        operand2 = Instruction(self.get_instruction_at_index(4))

        qword_operand1 = operand1.execute()
        qword_operand2 = operand2.execute()
        qubitset1 = self.get_last_qubitset(operand1.name, qword_operand1)
        qubitset2 = self.get_last_qubitset(operand2.name, qword_operand2)
        result = optimized_multiplication(qubitset1, qubitset2, Instruction.current_n, Instruction.bqm,
                                          Instruction.qubits_to_fix)
        return result


class Ite(Instruction):
    # TODO: Correct Optimization
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        sort = self.get_sort().execute()

        condition = Instruction(self.get_instruction_at_index(3))

        qword_condition = condition.execute()
        assert qword_condition.size_in_bits == 1

        if self.instruction[3][0] == '-':
            true_part = Instruction(self.get_instruction_at_index(5))
            false_part = Instruction(self.get_instruction_at_index(4))
        else:
            true_part = Instruction(self.get_instruction_at_index(4))
            false_part = Instruction(self.get_instruction_at_index(5))

        # assert true_qword.size_in_bits == sort.size_in_bits # this fails for memory

        # compute true part
        qubit_condition = self.get_last_qubitset(condition.name, qword_condition)
        assert len(qubit_condition) == 1

        result_qword = QWord(sort.size_in_bits)
        if qubit_condition[0] in Instruction.qubits_to_fix.keys():
            condition_value = Instruction.qubits_to_fix[qubit_condition[0]]
            if condition_value == 1:
                true_qword = true_part.execute()  # only execute true part if we actually need it (condition==1)
                qubitset1 = self.get_last_qubitset(true_part.name, true_qword)
                result_qword.append_state(qubitset1, Instruction.current_n)
            else:
                false_qword = false_part.execute()  # only execute true part if we actually need it (condition==0)
                qubitset2 = self.get_last_qubitset(false_part.name, false_qword)
                result_qword.append_state(qubitset2, Instruction.current_n)
            return result_qword

        true_qword = true_part.execute()
        false_qword = false_part.execute()
        assert true_qword.size_in_bits == false_qword.size_in_bits

        qubitset1 = self.get_last_qubitset(true_part.name, true_qword)
        qubitset2 = self.get_last_qubitset(false_part.name, false_qword)

        config_true_part = Config.AND
        config_false_part = Config.MATRIARCH1
        config_result = Config.OR

        current_bit = 0

        result_qubits = []
        condition_qubit = qubit_condition[0]
        while current_bit < len(qubitset1):
            true_qubit = qubitset1[current_bit]
            false_qubit = qubitset2[current_bit]

            condition_value = get_qubit_value(condition_qubit, Instruction.qubits_to_fix)
            true_value = get_qubit_value(true_qubit, Instruction.qubits_to_fix)
            false_value = get_qubit_value(false_qubit, Instruction.qubits_to_fix)

            if condition_value is not None:
                if condition_value == 0:
                    result_qubits.append(false_qubit)
                else:
                    result_qubits.append(true_qubit)
            elif true_value is not None and false_value is not None:
                if true_value == false_value:
                    result_qubits.append(false_qubit)
                else:
                    if true_value == 1 and false_value == 0:
                        # if Instruction.current_n > 18:
                        #result_qubits.append(qubit_condition[0])
                        # else:
                        temp_name = get_qubit_name()
                        Instruction.qubits_to_fix[temp_name] = 1
                        result_name = get_qubit_name()
                        model, _ = get_model(Config.AND, [temp_name, condition_qubit, result_name])
                        result_qubits.append(result_name)
                        InputPropagationFile.write_rule(R_AND, result_name, [qubit_condition[0], temp_name],
                                                        Instruction.qubits_to_fix)
                    else:
                        # true=0 and false=1
                        result_name = get_qubit_name()
                        model, _ = get_model(Config.NOT, [condition_qubit, result_name])
                        Instruction.bqm.update(model)
                        InputPropagationFile.write_rule(R_NOT, result_name, [condition_qubit],
                                                        Instruction.qubits_to_fix)
                        result_qubits.append(result_name)
            else:
                xi_name: int = get_qubit_name()
                yi_name: int = get_qubit_name()
                model_true, _ = get_model(config_true_part,
                                          [qubit_condition[0], qubitset1[current_bit], xi_name])

                model_false, _ = get_model(config_false_part,
                                           [qubit_condition[0], qubitset2[current_bit], yi_name])
                Instruction.bqm.update(model_false)

                result_name = get_qubit_name()
                model_result, _ = get_model(config_result, [xi_name, yi_name, result_name])
                Instruction.bqm.update(model_result)
                result_qubits.append(result_name)

                condition_value = get_qubit_value(qubit_condition[0], Instruction.qubits_to_fix)
                true_value = get_qubit_value(qubitset1[current_bit], Instruction.qubits_to_fix)
                false_value = get_qubit_value(qubitset2[current_bit], Instruction.qubits_to_fix)

                # try to constant propagate xi
                if condition_value is not None and true_value is not None:
                    Instruction.qubits_to_fix[xi_name] = condition_value and true_value
                elif condition_value == 0 or true_value == 0:
                    Instruction.qubits_to_fix[xi_name] = 0

                # try to constant propagate yi
                if condition_value is not None and false_value is not None:
                    Instruction.qubits_to_fix[yi_name] = (not condition_value) and false_value
                elif false_value == 0 or condition_value == 1:
                    Instruction.qubits_to_fix[yi_name] = 0

                xi_value = get_qubit_value(xi_name, Instruction.qubits_to_fix)
                yi_value = get_qubit_value(yi_name, Instruction.qubits_to_fix)

                if xi_value == 1 or yi_value == 1:
                    Instruction.qubits_to_fix[result_name] = 1
                elif xi_value is not None and yi_value is not None:
                    Instruction.qubits_to_fix[result_name] = xi_value or yi_value

                InputPropagationFile.write_rule(R_AND, xi_name, [qubit_condition[0], qubitset1[current_bit]],
                                                Instruction.qubits_to_fix)
                InputPropagationFile.write_rule(MATRIARCH1, yi_name, [qubit_condition[0], qubitset2[current_bit]],
                                                Instruction.qubits_to_fix)
                InputPropagationFile.write_rule(OR, result_name, [xi_name, yi_name], Instruction.qubits_to_fix)

            current_bit += 1

        assert len(result_qubits) == len(qubitset1)
        result_qword.append_state(result_qubits, Instruction.current_n)
        return result_qword


class Write(Instruction):
    # TODO: Correct optimization
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        memory = Instruction(self.get_instruction_at_index(3))
        memory_qword = memory.execute()
        qubits_memory = self.get_last_qubitset(memory.name, memory_qword)

        address = Instruction(self.get_instruction_at_index(4))
        address_qword = address.execute()
        qubits_address = self.get_last_qubitset(address.name, address_qword)
        # assert address_qword.size_in_bits >= ADDRESS_WORD_SIZE

        value = Instruction(self.get_instruction_at_index(5))
        value_qword = value.execute()
        qubits_value = self.get_last_qubitset(value.name, value_qword)
        assert len(qubits_value) == Instruction.WORD_SIZE

        is_address_constant = Instruction.is_constant(qubits_address)
        is_value_constant = Instruction.is_constant(qubits_value)
        result_qword = QWord(memory_qword.size_in_bits)
        result_qword.name = f"write_{Instruction.current_n}"
        if is_address_constant:
            # we know beforehand the address, no annealing needed
            address_in_binary = Instruction.get_fixed_bin_representation(qubits_address)
            address_in_decimal = get_decimal_representation(address_in_binary)
            try:
                local_memory_offset = Instruction.address_to_local_offsets[address_in_decimal]
            except:
                print(f"WARNING ({self.name}): address {address_in_decimal} not defined in addresspace, skipping")
                result_qword.append_state(qubits_memory, Instruction.current_n)
                return result_qword
            if is_value_constant:
                result_qubits = qubits_memory.copy()
                for i in range(Instruction.WORD_SIZE):
                    new_name = get_qubit_name()
                    result_qubits[local_memory_offset * Instruction.WORD_SIZE + i] = new_name
                    # qubit_name = qubits_memory[local_memory_offset*WORD_SIZE+i]
                    Instruction.qubits_to_fix[new_name] = Instruction.qubits_to_fix[qubits_value[i]]
                    linear, offset = get_model_single_var(Instruction.qubits_to_fix[qubits_value[i]])
                    Instruction.bqm.offset += offset
                    Instruction.bqm.add_variable(new_name, linear)
                result_qword.append_state(result_qubits, Instruction.current_n)
                return result_qword
            else:
                result_qubits = qubits_memory.copy()
                # if value is not a constant then we replace qubits names in memory to the names of
                # value we are trying to write in memory
                for i in range(Instruction.WORD_SIZE):
                    result_qubits[local_memory_offset * Instruction.WORD_SIZE + i] = qubits_value[i]
            result_qword.append_state(result_qubits, Instruction.current_n)
            return result_qword
        else:
            # we cant do constant propagation

            result_qubits = []
            for i in range(len(Instruction.addresses_qubits)):
                address_qubit = optimized_is_equal(Instruction.addresses_qubits[i],
                                                   qubits_address,
                                                   Instruction.current_n,
                                                   Instruction.bqm,
                                                   Instruction.qubits_to_fix
                                                   )[Instruction.current_n][0]

                # circuit to determine if bit is replaced by new value
                for j in range(i * Instruction.WORD_SIZE, (i * Instruction.WORD_SIZE) + Instruction.WORD_SIZE):
                    prev_qubit = qubits_memory[j]
                    current = qubits_value[j - (i * Instruction.WORD_SIZE)]

                    value_is_address = get_qubit_value(address_qubit, Instruction.qubits_to_fix)
                    prev_value = get_qubit_value(prev_qubit, Instruction.qubits_to_fix)
                    current_value = get_qubit_value(current, Instruction.qubits_to_fix)

                    if value_is_address is not None:
                        if value_is_address == 0:
                            result_qubits.append(prev_qubit)
                        else:
                            result_qubits.append(current)
                    elif prev_value is not None and current_value is not None:
                        if prev_value == current_value:
                            result_qubits.append(current)
                        else:
                            if prev_value == 0:
                                result_qubits.append(address_qubit)
                            else:
                                result_name = get_qubit_name()
                                model, _ = get_model(Config.NOT, [address_qubit, result_name])
                                InputPropagationFile.write_rule(R_NOT, result_name, [address_qubit],
                                                                Instruction.qubits_to_fix)
                                Instruction.bqm.update(model)
                                result_qubits.append(result_name)
                    elif prev_value == 0:
                        result_name = get_qubit_name()
                        model_r1, _ = get_model(Config.AND, [address_qubit, current, result_name])
                        Instruction.bqm.update(model_r1)
                        InputPropagationFile.write_rule(R_AND, result_name, [address_qubit, current],
                                                        Instruction.qubits_to_fix)
                        result_qubits.append(result_name)
                    elif current_value == 0:
                        result_name = get_qubit_name()
                        r2_config = Config.MATRIARCH1
                        model_r2, _ = get_model(r2_config, [address_qubit, prev_qubit, result_name])
                        InputPropagationFile.write_rule(MATRIARCH1, result_name, [address_qubit, prev_qubit],
                                                        Instruction.qubits_to_fix)
                        Instruction.bqm.update(model_r2)
                        result_qubits.append(result_name)
                    else:
                        new_memory_qubit = get_qubit_name()

                        # flow of current qubit
                        r1_config = Config.AND
                        r1 = get_qubit_name()

                        model_r1, _ = get_model(r1_config, [address_qubit, current, r1])
                        Instruction.bqm.update(model_r1)
                        InputPropagationFile.write_rule(R_AND, r1, [address_qubit, current], Instruction.qubits_to_fix)

                        r2_config = Config.MATRIARCH1
                        r2 = get_qubit_name()
                        model_r2, _ = get_model(r2_config, [address_qubit, prev_qubit, r2])
                        InputPropagationFile.write_rule(MATRIARCH1, r2, [address_qubit, prev_qubit],
                                                        Instruction.qubits_to_fix)
                        Instruction.bqm.update(model_r2)
                        new_memory_config = Config.OR
                        model_new_memory, _ = get_model(new_memory_config, [r1, r2, new_memory_qubit])
                        InputPropagationFile.write_rule(OR, new_memory_qubit, [r1, r2], Instruction.qubits_to_fix)
                        Instruction.bqm.update(model_new_memory)
                        result_qubits.append(new_memory_qubit)
        result_qword.append_state(result_qubits, Instruction.current_n)
        # print(len(result_qword[Instruction.current_n]), len(qubits_memory))
        # assert len(result_qword[Instruction.current_n]) == memory_qword.size_in_bits
        return result_qword


class Uext(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        sort = self.get_sort().execute()
        previous = Instruction(self.get_instruction_at_index(3))
        previous_qword = previous.execute()
        previous_qubits = self.get_last_qubitset(previous.name, previous_qword)

        ext_value = int(self.instruction[4])

        assert sort.size_in_bits == ext_value + previous_qword.size_in_bits

        result_qubits = previous_qubits.copy()  # we dont want references, instead deep copy list
        qword_result = QWord(sort.size_in_bits)
        qword_result.name = f"{self.id}{self.name}"
        while len(result_qubits) < sort.size_in_bits:
            name = get_qubit_name()
            result_qubits.append(name)
            Instruction.qubits_to_fix[name] = 0
            linear, offset = get_model_single_var(0)
            Instruction.bqm.add_variable(name, linear)
            Instruction.bqm.offset += offset
        qword_result.append_state(result_qubits, Instruction.current_n)
        return qword_result


class And(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        operand1 = Instruction(self.get_instruction_at_index(3))
        operand1_qword = operand1.execute()
        operand2 = Instruction(self.get_instruction_at_index(4))
        operand2_qword = operand2.execute()

        bitset1 = self.get_last_qubitset(operand1.name, operand1_qword)
        bitset2 = self.get_last_qubitset(operand2.name, operand2_qword)

        result_qword = optimized_bitwise_and(bitset1, bitset2, Instruction.current_n, Instruction.bqm,
                                             Instruction.qubits_to_fix)
        return result_qword


class Not(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> QWord:
        operand1 = Instruction(self.get_instruction_at_index(3))
        operand1_qword = operand1.execute()
        bitset1 = self.get_last_qubitset(operand1.name, operand1_qword)
        result = optimized_bitwise_not(bitset1, Instruction.current_n, Instruction.bqm, Instruction.qubits_to_fix)
        return result


class Eq(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        operand1 = Instruction(self.get_instruction_at_index(3))
        operand1_qword = operand1.execute()

        operand2 = Instruction(self.get_instruction_at_index(4))
        operand2_qword = operand2.execute()

        bitset1 = self.get_last_qubitset(operand1.name, operand1_qword)
        bitset2 = self.get_last_qubitset(operand2.name, operand2_qword)

        result = optimized_is_equal(bitset1, bitset2, Instruction.current_n, Instruction.bqm, Instruction.qubits_to_fix)
        return result


class Neq(Instruction):

    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> QWord:
        operand1 = Instruction(self.get_instruction_at_index(3))
        operand1_qword = operand1.execute()

        operand2 = Instruction(self.get_instruction_at_index(4))
        operand2_qword = operand2.execute()
        bitset1 = self.get_last_qubitset(operand1.name, operand1_qword)
        bitset2 = self.get_last_qubitset(operand2.name, operand2_qword)
        temp_result = optimized_xor(bitset1, bitset2, Instruction.bqm, Instruction.qubits_to_fix)
        result = optimized_bits_or(temp_result, Instruction.bqm, Instruction.qubits_to_fix)
        result_qword = QWord(1)
        result_qword.append_state([result], Instruction.current_n)
        return result_qword


class Ult(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        operand1 = Instruction(self.get_instruction_at_index(3))
        operand1_qword = operand1.execute()

        operand2 = Instruction(self.get_instruction_at_index(4))
        operand2_qword = operand2.execute()

        bitset1 = self.get_last_qubitset(operand1.name, operand1_qword)
        bitset2 = self.get_last_qubitset(operand2.name, operand2_qword)
        result = optimized_unsigned_less_than(bitset1, bitset2, Instruction.current_n, Instruction.bqm,
                                              Instruction.qubits_to_fix)

        return result


class Ulte(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        operand1 = Instruction(self.get_instruction_at_index(3))
        operand1_qword = operand1.execute()

        operand2 = Instruction(self.get_instruction_at_index(4))
        operand2_qword = operand2.execute()

        bitset1 = self.get_last_qubitset(operand1.name, operand1_qword)
        bitset2 = self.get_last_qubitset(operand2.name, operand2_qword)

        result = optimized_unsigned_lte(bitset1, bitset2, Instruction.current_n, Instruction.bqm,
                                        Instruction.qubits_to_fix)

        return result


class Ugt(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        operand1 = Instruction(self.get_instruction_at_index(3))
        operand1_qword = operand1.execute()

        operand2 = Instruction(self.get_instruction_at_index(4))
        operand2_qword = operand2.execute()

        bitset1 = self.get_last_qubitset(operand1.name, operand1_qword)
        bitset2 = self.get_last_qubitset(operand2.name, operand2_qword)

        result = optimized_unsigned_greater_than(bitset1, bitset2, Instruction.current_n, Instruction.bqm,
                                                 Instruction.qubits_to_fix)

        return result


class Ugte(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        operand1 = Instruction(self.get_instruction_at_index(3))
        operand1_qword = operand1.execute()

        operand2 = Instruction(self.get_instruction_at_index(4))
        operand2_qword = operand2.execute()

        bitset1 = self.get_last_qubitset(operand1.name, operand1_qword)
        bitset2 = self.get_last_qubitset(operand2.name, operand2_qword)
        result = optimized_unsigned_gte(bitset1, bitset2, Instruction.current_n, Instruction.bqm,
                                        Instruction.qubits_to_fix)

        return result


class Udiv(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        operand1 = Instruction(self.get_instruction_at_index(3))
        operand1_qword = operand1.execute()

        operand2 = Instruction(self.get_instruction_at_index(4))
        operand2_qword = operand2.execute()
        bitset1 = self.get_last_qubitset(operand1.name, operand1_qword)
        bitset2 = self.get_last_qubitset(operand2.name, operand2_qword)

        result = optimized_get_quotient(bitset1, bitset2, Instruction.current_n, Instruction.bqm,
                                        Instruction.qubits_to_fix)
        return result


class Urem(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        operand1 = Instruction(self.get_instruction_at_index(3))
        operand1_qword = operand1.execute()

        operand2 = Instruction(self.get_instruction_at_index(4))
        operand2_qword = operand2.execute()

        bitset1 = self.get_last_qubitset(operand1.name, operand1_qword)
        bitset2 = self.get_last_qubitset(operand2.name, operand2_qword)
        assert len(bitset1) == len(bitset2)
        if Instruction.is_constant(bitset1) and Instruction.is_constant(bitset2):
            bitset1_in_binary = Instruction.get_fixed_bin_representation(bitset1)
            bitset2_in_binary = Instruction.get_fixed_bin_representation(bitset2)
            bitset1_in_decimal = get_decimal_representation(bitset1_in_binary)
            bitset2_in_decimal = get_decimal_representation(bitset2_in_binary)
            result_in_decimal = bitset1_in_decimal % bitset2_in_decimal

            result_in_binary = get_bit_repr_of_number(result_in_decimal, len(bitset1))
            result_qubitset = []
            for res in result_in_binary:
                qubit_name = get_qubit_name()
                Instruction.qubits_to_fix[qubit_name] = res
                result_qubitset.append(qubit_name)
                linear, offset = get_model_single_var(res)
                Instruction.bqm.add_variable(qubit_name, linear)
                Instruction.bqm.offset += offset
            qword_result = QWord(len(bitset1))
            qword_result.append_state(result_qubitset, Instruction.current_n)
            return qword_result
        else:
            raise Exception("non constant operands on UREM not implemented")


class Read(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        sort = self.get_sort().execute()
        memory = Instruction(self.get_instruction_at_index(3))
        memory_qword = memory.execute()
        qubits_memory = self.get_last_qubitset(memory.name, memory_qword)

        address = Instruction(self.get_instruction_at_index(4))
        address_qword = address.execute()

        qubits_address = self.get_last_qubitset(address.name, address_qword)

        assert Instruction.WORD_SIZE == sort.size_in_bits
        is_address_constant = Instruction.is_constant(qubits_address)

        if is_address_constant:
            result_qword = QWord(Instruction.WORD_SIZE)

            result_qubitset = []
            address_in_binary = Instruction.get_fixed_bin_representation(qubits_address)
            address_in_decimal = get_decimal_representation(address_in_binary)

            try:
                local_memory_offset = Instruction.address_to_local_offsets[address_in_decimal]
                for i in range(Instruction.WORD_SIZE):
                    qubit_name = qubits_memory[local_memory_offset * Instruction.WORD_SIZE + i]
                    result_qubitset.append(qubit_name)
            except:
                print(f"WARNING ({self.name}): address {address_in_decimal} not defined in addresspace, skipping")
                for i in range(Instruction.WORD_SIZE):
                    qubit_name = get_qubit_name()
                    result_qubitset.append(qubit_name)
                    Instruction.bqm.add_variable(qubit_name)
                    Instruction.qubits_to_fix[qubit_name] = 0
            result_qword.append_state(result_qubitset, Instruction.current_n)

            return result_qword
        else:

            words_to_compare: List[List[int]] = []
            for i in range(len(Instruction.addresses_qubits)):
                is_address = optimized_is_equal(Instruction.addresses_qubits[i],
                                                qubits_address,
                                                Instruction.current_n,
                                                Instruction.bqm,
                                                Instruction.qubits_to_fix
                                                )[Instruction.current_n][0]
                # is_address = is_equal(Instruction.addresses_qubits[i][Instruction.word_lsb_index:],
                #                       qubits_address[Instruction.word_lsb_index:],
                #                       Instruction.current_n,
                #                       Instruction.bqm,
                #                       )[Instruction.current_n][0]

                actual_word: List[int] = []
                for j in range(i * Instruction.WORD_SIZE, (i * Instruction.WORD_SIZE) + Instruction.WORD_SIZE):
                    actual_qubit = qubits_memory[j]
                    if not (is_address in Instruction.qubits_to_fix.keys()):
                        if not (actual_qubit in Instruction.qubits_to_fix.keys()):
                            bit_name = get_qubit_name()
                            model, _ = get_model(Config.AND, [is_address, actual_qubit, bit_name])
                            Instruction.bqm.update(model)
                            actual_word.append(bit_name)
                            InputPropagationFile.write_rule(R_AND, bit_name,
                                                            [is_address, actual_qubit],
                                                            Instruction.qubits_to_fix)
                        else:
                            value_actual_qubit = Instruction.qubits_to_fix[actual_qubit]
                            if value_actual_qubit == 0:
                                actual_word.append(actual_qubit)
                            else:
                                actual_word.append(is_address)
                    else:
                        value_address_bit = Instruction.qubits_to_fix[is_address]
                        if actual_qubit in Instruction.qubits_to_fix.keys():
                            value_actual_qubit = Instruction.qubits_to_fix[actual_qubit]
                            bit_name = get_qubit_name()

                            Instruction.qubits_to_fix[bit_name] = value_address_bit and value_actual_qubit
                            linear, offset = get_model_single_var(Instruction.qubits_to_fix[bit_name])
                            Instruction.bqm.add_variable(bit_name, linear)
                            Instruction.bqm.offset += offset
                            actual_word.append(bit_name)
                        else:
                            if value_address_bit == 0:
                                bit_name = get_qubit_name()
                                Instruction.qubits_to_fix[bit_name] = 0
                                linear, offset = get_model_single_var(Instruction.qubits_to_fix[bit_name])
                                Instruction.bqm.add_variable(bit_name, linear)
                                Instruction.bqm.offset += offset
                                actual_word.append(bit_name)
                            else:
                                actual_word.append(actual_qubit)
                words_to_compare.append(actual_word)
            # perform logic OR over all words

            assert len(words_to_compare) == len(Instruction.addresses_qubits)
            if len(words_to_compare) == 0:
                raise Exception("Memory is of size 0. Cannot perform read instruction.")

            assert Instruction.WORD_SIZE == sort.size_in_bits

            qword_result = QWord(Instruction.WORD_SIZE)
            if len(words_to_compare) == 1:
                qword_result.append_state(words_to_compare[0], Instruction.current_n)
                return qword_result
            else:
                bitset_result = optimized_bitwise_or(words_to_compare[0], words_to_compare[1], Instruction.current_n,
                                                     Instruction.bqm, Instruction.qubits_to_fix)
                for bitset_index in range(2, len(words_to_compare)):
                    previous_result = bitset_result[Instruction.current_n]
                    bitset_result = optimized_bitwise_or(previous_result, words_to_compare[bitset_index],
                                                         Instruction.current_n,
                                                         Instruction.bqm, Instruction.qubits_to_fix)

                return bitset_result


class Bad(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        bad_state = Instruction(self.get_instruction_at_index(2))
        bad_state_qword = bad_state.execute()
        bad_state_qubits = bad_state_qword.top
        assert bad_state_qword.size_in_bits == 1
        # Instruction.qubits_to_fix[bad_state_qubits[0]] = 1  # make the bad state happen
        qword_result = QWord(1)
        qword_result.append_state([bad_state_qubits[0]], Instruction.current_n)
        Instruction.bad_states.append(bad_state_qubits[0])
        Instruction.bad_states_to_line_no[bad_state_qubits[0]] = self.id
        return qword_result


class Slice(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> QWord:
        sort = self.get_sort().execute()

        operand = Instruction(self.get_instruction_at_index(3))
        qword = operand.execute()
        qubitset = self.get_last_qubitset(operand.name, qword)

        bottom = int(self.instruction[5])
        top = int(self.instruction[4])

        result_qubits = []
        for i in range(bottom, top + 1):
            result_qubits.append(qubitset[i])

        assert len(result_qubits) == (top - bottom) + 1
        result_qword = QWord(sort.size_in_bits)
        result_qword.append_state(result_qubits, Instruction.current_n)

        return result_qword
