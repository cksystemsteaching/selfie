from typing import Optional

from settings import *
from utils import *
from qword_tools import *
from qiskit import QuantumCircuit


class Instruction:
    # BEGIN static attributes
    all_instructions: Dict[int, List[str]] = {}  # maps <sid> -> (list of tokens of the instruction)
    current_n = 0
    circuit: QuantumCircuit = QuantumCircuit()
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
    input_nids: List[QWord] = []
    ONE_CONST: QuantumRegister = QuantumRegister(1)
    ZERO_CONST: QuantumRegister = QuantumRegister(1)
    global_stack: Stack = Stack()
    with_grover: int = 0
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

    counter = 0

    # END static attributes

    @staticmethod
    def clean_static_variables():
        Instruction.all_instructions = {}
        Instruction.current_n = 0
        Instruction.circuit = QuantumCircuit()
        Instruction.qubits_end_data_segment = None
        Instruction.qubits_end_heap = None
        Instruction.addresses_qubits = []
        Instruction.created_states_ids = {}
        Instruction.address_to_local_offsets = {}
        Instruction.bad_states = []
        Instruction.bad_states_to_line_no = {}
        Instruction.input_nids = []
        Instruction.global_stack = Stack()

    @staticmethod
    def set_setting(setting):
        Instruction.ADDRESS_WORD_SIZE = setting['address_word_size']
        Instruction.ADDRESS_STEP_SIZE = setting['address_step_size']
        Instruction.BEGIN_DATASEGMENT = setting['begin_datasegment']
        Instruction.SIZE_DATASEGMENT = setting['size_datasegment']
        Instruction.BEGIN_HEAP = setting['begin_heap']
        Instruction.SIZE_HEAP = setting['size_heap']
        Instruction.BEGIN_STACK = setting['begin_stack']
        Instruction.SIZE_STACK = setting['size_stack']
        Instruction.WORD_SIZE = setting['word_size']


    @staticmethod
    def get_input_qubits() -> QuantumRegister:
        input_qubits = []
        for qword in Instruction.input_nids:
            for timestep in range(Instruction.current_n+1):
                if timestep in qword.states.keys():
                    register, _ = qword[timestep]
                    input_qubits.extend(register[:])
        return QuantumRegister(bits=input_qubits)

    def __init__(self, instruction: List[str]):

        self.qubit_prefix = f"{instruction[1]}"
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

    def get_last_qubitset(self, name: str, qword: QWord) -> (QuantumRegister, List[int]):
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

    def raise_error(self, c):
        pass
        # print(self.id, self.name, get_decimal_representation(c))

    def execute(self) -> Optional[QWord]:

        if self.name in [NEXT, SORT, INIT]:
            result = self.specific_subclass.execute()

            return result

        if isinstance(self.specific_subclass, State):
            result = self.specific_subclass.execute()
            _, consts = self.get_last_qubitset(STATE, result)
            if QWord.are_all_constants(consts):
                self.raise_error(consts)
            # else:
            #     print(self.id, self.name, "not constant")
            return result

        if self.id in Instruction.created_states_ids.keys():
            if self.name in [CONSTD, ONE, ZERO]:
                # for these values we only access timestep 0. If the id-key exists then dont worry processing.
                self.specific_subclass.execute()
                result = Instruction.created_states_ids[self.id]
                _, consts = self.get_last_qubitset(self.name, result)
                if QWord.are_all_constants(consts):
                    self.raise_error(consts)
                # else:
                #     print(self.id, self.name, "not constant")
                return result

            if self.current_n in Instruction.created_states_ids[self.id].states.keys():
                pass
            else:
                result_qword = self.specific_subclass.execute()
                # assert len(result_qword.states) == 1
                state, consts = result_qword.top
                Instruction.created_states_ids[self.id].append_state(state, consts, Instruction.current_n)
        else:

            result_qword = self.specific_subclass.execute()
            assert len(result_qword.states) == 1
            Instruction.created_states_ids[self.id] = result_qword
        _, consts = self.get_last_qubitset(self.name, Instruction.created_states_ids[self.id])
        if QWord.are_all_constants(consts):
            self.raise_error(consts)
        # else:
        #     print(self.id, self.name, "not constant")
        return Instruction.created_states_ids[self.id]

    @staticmethod
    def get_constant_register(c, size):
        # result = []
        qr = QuantumRegister(size)
        Instruction.circuit.add_register(qr)
        for q in qr:
            if c % 2 == 1:
                Instruction.circuit.x(q)
                Instruction.global_stack.push(Element(GATE_TYPE, X, [], q))
            c = c//2
        return qr

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
                Instruction.addresses_qubits.append(Instruction.get_constant_register(address,
                                                                                      Instruction.ADDRESS_WORD_SIZE))
                Instruction.address_to_local_offsets[address] = local_offset
                local_offset += 1

            # create addresses for heap
            for address_index in range(Instruction.SIZE_HEAP):
                address = Instruction.BEGIN_HEAP + Instruction.ADDRESS_STEP_SIZE * address_index
                Instruction.addresses_qubits.append(Instruction.get_constant_register(address,
                                                                                      Instruction.ADDRESS_WORD_SIZE))
                Instruction.address_to_local_offsets[address] = local_offset
                local_offset += 1

            # create_addresses for stack
            for address_index in range(Instruction.SIZE_STACK):
                # consider that stack grows downwards
                address = Instruction.BEGIN_STACK - Instruction.ADDRESS_STEP_SIZE * (address_index + 1)
                Instruction.addresses_qubits.append(Instruction.get_constant_register(address,
                                                                                      Instruction.ADDRESS_WORD_SIZE))
                Instruction.address_to_local_offsets[address] = local_offset
                local_offset += 1

    @staticmethod
    def is_constant(qubit_names):
        for name in qubit_names:
            if Instruction.qubits_to_fix.get(name) is None:
                return False
        return True

    @staticmethod
    def or_bad_states() -> Optional[QuantumRegister]:
        if len(Instruction.bad_states) > 0:
            result = QuantumRegister(1)
            Instruction.circuit.add_register(result)
            consts = [0]
            logic_or(Instruction.bad_states, result[0], [-1 for _ in Instruction.bad_states] ,consts,
                     Instruction.circuit, Instruction.global_stack)
            return result  # returns the qubit name
        else:
            print("No bad state qubits!")
            return None


class Init(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self):
        operand1 = Instruction(self.get_instruction_at_index(3))
        qword1 = operand1.execute()
        qubit_set1, constants1 = qword1[0]

        operand2 = Instruction(self.get_instruction_at_index(4))
        qword2 = operand2.execute()
        qubit_set2, constants2 = self.get_last_qubitset(operand2.name, qword2)

        for (index, qubit_name) in enumerate(qubit_set2):
            assert (constants1[index] != -1)
            if constants1[index] != constants2[index]:
                Instruction.circuit.x(qubit_set1[index])
                constants1[index] = int((constants1[index]+1) % 2)
                Instruction.global_stack.push(Element(GATE_TYPE, X, [], qubit_set1[index]))

        qword1.append_state(qubit_set2, constants2, 1)
        return qword1


class Input(Instruction):

    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        sort = self.get_sort().execute()
        if self.id in Instruction.created_states_ids.keys():
            # if already exists a hashmap for this id
            result_qword = Instruction.created_states_ids[self.id]
            #
            # # we need a set of qubits for the current timestep
            if not (Instruction.current_n in Instruction.created_states_ids[self.id].states.keys()):
                qubits, constants = result_qword.create_state(Instruction.circuit, Instruction.current_n)
                # result_qword.states[Instruction.current_n] = (qubits, get_bit_repr_of_number(49, sort.size_in_bits))
                for (index, q) in enumerate(qubits):
                    Instruction.circuit.h(q)
                    constants[index] = -1

        else:
            # this instruction's id does not exists yet.
            result_qword = QWord(sort.size_in_bits, f"in{self.id}")
            qubits, constants = result_qword.create_state(Instruction.circuit, 1, set_name=True)
            # result_qword.states[1] = (qubits, get_bit_repr_of_number(49, sort.size_in_bits))
            for (index, q) in enumerate(qubits):
                Instruction.circuit.h(q)
                constants[index] = -1
            Instruction.created_states_ids[self.id] = result_qword
            Instruction.input_nids.append(Instruction.created_states_ids[self.id])
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
            sort = self.get_sort()
            qword = sort.execute()
            # qword.name = self.name

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

            qubits, constants = qword.create_state(Instruction.circuit, 0)
            if Instruction.initialize_states and self.instruction[1] in [CONSTD, ONE]:
                # if flag is turn on or we are dealing with constants then we initialize this state/constant
                for (index, bit) in enumerate(bit_representation):
                    if bit == 1:
                        Instruction.circuit.x(qubits[index])
                        constants[index] = 1
                        assert(qword[0][1][index] == 1)
                        Instruction.global_stack.push(Element(GATE_TYPE, X, [], qubits[index]))
        return Instruction.created_states_ids[self.id]


class Next(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        previous_state = Instruction(self.get_instruction_at_index(3)).execute()
        future_state = Instruction(self.get_instruction_at_index(4))
        qword_future = future_state.execute()  # gets bitvector of the 2nd operand
        if previous_state and future_state:
            qubits, constants = self.get_last_qubitset(future_state.name, qword_future)
            #print("future length ", len(constants), len(qubits))
            previous_state.append_state(qubits, constants, Instruction.current_n)
        else:
            # if for some reason, evaluating one of the operands returns None we throw an error
            raise Exception(f"not valid transition: {self}")
        return None


# Arithmetic operations
class Add(Instruction):

    # TODO: optimization
    def __init__(self, instruction):
        super(Add, self).__init__(instruction)

    def execute(self) -> Optional[QWord]:
        sort = self.get_sort().execute().size_in_bits
        qword_result = QWord(sort, self.name)
        qword_result.create_state(Instruction.circuit, Instruction.current_n)

        if self.name == INC or self.name == DEC:
            qword_result.create_ancillas(Instruction.current_n, sort, Instruction.circuit)
            if self.name == INC:
                qword_result.ancillas[Instruction.current_n] = self.get_constant_register(1, sort)
            else:
                # is decrementing by 1
                qword_result.ancillas[Instruction.current_n] = self.get_constant_register(-1, sort)

        local_stack = None
        operand1 = Instruction(self.get_instruction_at_index(3))
        qword1 = operand1.execute()
        qubit_set1, constants1 = self.get_last_qubitset(operand1.name, qword1)
        consts2 = None
        if self.instruction[1] == ADD:
            operand2 = Instruction(self.get_instruction_at_index(4))
            qword2 = operand2.execute()
            qubit_set2, constants2 = self.get_last_qubitset(operand2.name, qword2)
        elif self.instruction[1] == SUB:
            operand2 = Instruction(self.get_instruction_at_index(4))
            qword2 = operand2.execute()
            qubit_set2, constants2 = self.get_last_qubitset(operand2.name, qword2)
            consts2 = constants2[:]
            local_stack = optimized_get_twos_complement(qubit_set2, consts2, Instruction.circuit, Instruction.global_stack)
        else:
            qubit_set2 = qword_result.ancillas[Instruction.current_n]
            if self.name == INC:
                constants2 = get_bit_repr_of_number(1, sort)
            else:
                # is decrementing by 1
                constants2 = get_bit_repr_of_number(-1, sort)

        assert len(qubit_set1) == len(qubit_set2)
        assert len(qubit_set1) == sort


        if local_stack is not None:
            assert(consts2 is not None)
            optimized_bitwise_add(qubit_set1, qubit_set2, qword_result, constants1, consts2,
                                  Instruction.circuit, Instruction.global_stack, Instruction.current_n)
            # uncomputes twos complement
            while not local_stack.is_empty():
                element = local_stack.pop()
                element.apply(Instruction.circuit)
                Instruction.global_stack.push(element)
        else:
            optimized_bitwise_add(qubit_set1, qubit_set2, qword_result, constants1, constants2,
                                  Instruction.circuit, Instruction.global_stack, Instruction.current_n)

        if QWord.are_all_constants(constants1) and QWord.are_all_constants(constants2):
            if self.name != SUB:
                dec1 = get_decimal_representation(constants1)
                dec2 = get_decimal_representation(constants2)
                res = (dec1 + dec2) & (2**len(constants1)-1)
                assert(res == get_decimal_representation(qword_result[Instruction.current_n][1]))
            else:
                dec1 = get_decimal_representation(constants1)
                dec2 = get_decimal_representation(consts2)
                res = (dec1 + dec2) & (2**len(constants1)-1)
                assert ( res == get_decimal_representation(qword_result[Instruction.current_n][1]))


        return qword_result


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
        bitset1, constants1 = self.get_last_qubitset(operand1.name, qword_operand1)
        bitset2, constants2 = self.get_last_qubitset(operand2.name, qword_operand2)

        qword_result = QWord(len(bitset1), self.name)
        qword_result.create_state(Instruction.circuit, Instruction.current_n, True)
        qword_result.create_ancillas(Instruction.current_n, len(bitset1), Instruction.circuit)
        optimized_mul(bitset1, bitset2, qword_result, constants1, constants2, Instruction.circuit,
                      qword_result.ancillas[Instruction.current_n], Instruction.global_stack, Instruction.current_n)

        if QWord.are_all_constants(constants1) and QWord.are_all_constants(constants2):
            assert(QWord.are_all_constants(qword_result[Instruction.current_n][1]))
            assert(get_decimal_representation(constants1) * get_decimal_representation(constants2) ==
                   get_decimal_representation(qword_result[Instruction.current_n][1]))
        return qword_result


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
        qubit_condition, const_condition = self.get_last_qubitset(condition.name, qword_condition)

        assert len(qubit_condition) == 1

        result_qword = QWord(sort.size_in_bits)
        # print(self.instruction)
        # print(const_condition[0])
        if const_condition[0] != -1:
            if const_condition[0] == 1:
                true_qword = true_part.execute()  # only execute true part if we actually need it (condition==1)
                qubitset1, consts1 = self.get_last_qubitset(true_part.name, true_qword)
                result_qword.append_state(qubitset1, consts1, Instruction.current_n)

            else:
                false_qword = false_part.execute()  # only execute true part if we actually need it (condition==0)
                qubitset2, consts2 = self.get_last_qubitset(false_part.name, false_qword)
                result_qword.append_state(qubitset2, consts2, Instruction.current_n)
            return result_qword

        assert(const_condition[0] == -1)
        true_part_qword = true_part.execute()
        true_part_bits, constants_true_part = self.get_last_qubitset(true_part.name, true_part_qword)

        false_part_qword = false_part.execute()
        false_part_bits, constants_false_part = self.get_last_qubitset(false_part.name, false_part_qword)
        result_bits, result_consts = result_qword.create_state(Instruction.circuit, Instruction.current_n)

        for (index, result_bit) in enumerate(result_bits):

            Instruction.circuit.ccx(qubit_condition[0], true_part_bits[index], result_bit)
            Instruction.global_stack.push(Element(GATE_TYPE, CCX, [qubit_condition[0], true_part_bits[index]],
                                                  result_bit))

        Instruction.circuit.x(qubit_condition[0])
        Instruction.global_stack.push(Element(GATE_TYPE, X, [], qubit_condition[0]))
        for (index, result_bit) in enumerate(result_bits):
            Instruction.circuit.ccx(qubit_condition[0], false_part_bits[index], result_bit)
            Instruction.global_stack.push(Element(GATE_TYPE, CCX, [qubit_condition[0], false_part_bits[index]],
                                                  result_bit))
        Instruction.circuit.x(qubit_condition[0])
        Instruction.global_stack.push(Element(GATE_TYPE, X, [], qubit_condition[0]))

        # constant propagation
        for (index, (const_true_part, const_false_part)) in enumerate(zip(constants_true_part,
                                                                          constants_false_part)):
            if const_true_part == const_false_part:
                if const_true_part == -1:
                    result_consts[index] = -1
                else:
                    result_consts[index] = const_true_part
            else:
                result_consts[index] = -1
        return result_qword


class Write(Instruction):
    # TODO: Correct optimization
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        raise Exception("Not implemented")


class Uext(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        sort = self.get_sort().execute().size_in_bits
        previous = Instruction(self.get_instruction_at_index(3))
        previous_qword = previous.execute()
        previous_qubits, constants_op = self.get_last_qubitset(previous.name, previous_qword)
        constants = [0 for _ in range(sort)]

        ext_value = int(self.instruction[4])

        assert sort == ext_value + previous_qword.size_in_bits

        result = QWord(sort, self.name)
        result.create_ancillas(Instruction.current_n, ext_value, Instruction.circuit)

        result_qubits = []

        for (i, qubit) in enumerate(previous_qubits):
            result_qubits.append(qubit)
            constants[i] = constants_op[i]

        for qubit in result.ancillas[Instruction.current_n]:
            result_qubits.append(qubit)

        result.append_state(QuantumRegister(bits=result_qubits), constants, Instruction.current_n)
        return result


class And(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        operand1 = Instruction(self.get_instruction_at_index(3))
        operand1_qword = operand1.execute()
        operand2 = Instruction(self.get_instruction_at_index(4))
        operand2_qword = operand2.execute()

        bitset1, constants1 = self.get_last_qubitset(operand1.name, operand1_qword)
        bitset2, constants2 = self.get_last_qubitset(operand2.name, operand2_qword)

        result_qword = QWord(self.get_sort().execute().size_in_bits, self.name)
        result_qword.create_state(Instruction.circuit, Instruction.current_n)
        optimized_bitwise_and(bitset1, bitset2, result_qword, constants1, constants2, Instruction.circuit,
                              Instruction.global_stack, Instruction.current_n)
        # if QWord.are_all_constants(constants1) and QWord.are_all_constants(constants2):
        #     assert(QWord.are_all_constants(result_qword[Instruction.current_n][1]))
        #     assert(get_decimal_representation(constants1) & get_decimal_representation(constants2) ==
        #            get_decimal_representation(result_qword[Instruction.current_n][1]))
        return result_qword


class Not(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> QWord:
        operand1 = Instruction(self.get_instruction_at_index(3))
        operand1_qword = operand1.execute()
        x, constants = self.get_last_qubitset(operand1.name, operand1_qword)
        result = QWord(self.get_sort().execute().size_in_bits, self.name)
        res_reg, res_consts = result.create_state(Instruction.circuit, Instruction.current_n)
        optimized_bitwise_not(x, res_reg, constants, res_consts, Instruction.circuit, Instruction.global_stack)
        if QWord.are_all_constants(constants):
            for (index,c) in enumerate(constants):
                assert(res_consts[index] == ((c+1)%2))
        return result


class Eq(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        operand1 = Instruction(self.get_instruction_at_index(3))
        operand1_qword = operand1.execute()

        operand2 = Instruction(self.get_instruction_at_index(4))
        operand2_qword = operand2.execute()

        bitset1, constants1 = self.get_last_qubitset(operand1.name, operand1_qword)
        bitset2, constants2 = self.get_last_qubitset(operand2.name, operand2_qword)

        result_qword = QWord(1, self.name)
        result_qword.create_state(Instruction.circuit, Instruction.current_n, True)
        ancillas = result_qword.create_ancillas(Instruction.current_n, len(bitset1) + 1,
                                                Instruction.circuit)

        optimized_is_equal(bitset1, bitset2, result_qword, constants1, constants2, Instruction.circuit, ancillas,
                           Instruction.global_stack, Instruction.current_n)
        if QWord.are_all_constants(constants1) and QWord.are_all_constants(constants2):
            assert((get_decimal_representation(constants1) == get_decimal_representation(constants2))
                   == result_qword[Instruction.current_n][1][0])
        return result_qword


class Neq(Instruction):

    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> QWord:
        operand1 = Instruction(self.get_instruction_at_index(3))
        operand1_qword = operand1.execute()

        operand2 = Instruction(self.get_instruction_at_index(4))
        operand2_qword = operand2.execute()
        bitset1, constants1 = self.get_last_qubitset(operand1.name, operand1_qword)
        bitset2, constants2 = self.get_last_qubitset(operand2.name, operand2_qword)
        result_qword = QWord(1, self.name)
        result_bits, result_constants = result_qword.create_state(Instruction.circuit, Instruction.current_n)
        ancillas = result_qword.create_ancillas(Instruction.current_n, len(bitset1) + 1,
                                                Instruction.circuit)
        Instruction.circuit.x(ancillas[ancillas.size - 1])
        optimized_is_equal(bitset1, bitset2, result_qword, constants1, constants2, Instruction.circuit, ancillas,
                           Instruction.global_stack, Instruction.current_n)
        assert (result_qword.size_in_bits == 1)
        Instruction.circuit.x(result_bits[0])
        Instruction.global_stack.push(Element(GATE_TYPE, X, [], result_bits[0]))
        if result_constants[0] != -1:
            result_constants[0] += 1
            result_constants[0] = int(result_constants[0] % 2)

        if QWord.are_all_constants(constants1) and QWord.are_all_constants(constants2):
            assert((get_decimal_representation(constants1) != get_decimal_representation(constants2))
                   == result_qword[Instruction.current_n][1][0])
        return result_qword


class Ult(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        sort = self.get_sort().execute().size_in_bits
        operand1 = Instruction(self.get_instruction_at_index(3))
        operand1_qword = operand1.execute()

        operand2 = Instruction(self.get_instruction_at_index(4))
        operand2_qword = operand2.execute()

        bitset1, constants1 = self.get_last_qubitset(operand1.name, operand1_qword)
        bitset2, constants2 = self.get_last_qubitset(operand2.name, operand2_qword)
        result_qword = QWord(1, self.name)
        result_qword.create_state(Instruction.circuit, Instruction.current_n)
        # ancillas = 2 ancillas to add to each operand to perform substraction, sort to store the addition
        # (we actually need sort+1 to store addition, but we use result_qword to store the MSB).
        ancillas = result_qword.create_ancillas(Instruction.current_n, 2 + len(bitset1), Instruction.circuit)
        optimized_unsigned_ult(bitset1, bitset2, result_qword, constants1, constants2, Instruction.circuit,
                               ancillas, Instruction.global_stack, Instruction.current_n)
        if QWord.are_all_constants(constants1) and QWord.are_all_constants(constants2):
            assert((get_decimal_representation(constants1) < get_decimal_representation(constants2))
                   == result_qword[Instruction.current_n][1][0])
        return result_qword


class Ulte(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:

        operand1 = Instruction(self.get_instruction_at_index(3))
        operand1_qword = operand1.execute()

        operand2 = Instruction(self.get_instruction_at_index(4))
        operand2_qword = operand2.execute()

        bitset1, constants1 = self.get_last_qubitset(operand1.name, operand1_qword)
        bitset2, constants2 = self.get_last_qubitset(operand2.name, operand2_qword)

        sort = len(bitset1)

        result_qword = QWord(1, self.name)
        result_qword.create_state(Instruction.circuit, Instruction.current_n)
        # ancillas =
        # LTE uses: 2 ancillas to add to each operand to perform substraction, sort to store the addition
        # (we actually need sort+1 to store addition, but we use result_qword to store the MSB).

        # 1 ancilla to save the result of LTE
        # 1 ancilla to save the result of EQ
        # EQ uses sort+1 ancillas
        ancillas = result_qword.create_ancillas(Instruction.current_n, 2 + sort + 2 + sort +1, Instruction.circuit)
        optimized_unsigned_ulte(bitset1, bitset2, result_qword, constants1, constants2, Instruction.circuit, ancillas,
                                Instruction.global_stack, Instruction.current_n)

        if QWord.are_all_constants(constants1) and QWord.are_all_constants(constants2):
            assert((get_decimal_representation(constants1) <= get_decimal_representation(constants2))
                   == result_qword[Instruction.current_n][1][0])
        return result_qword


class Ugt(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        operand1 = Instruction(self.get_instruction_at_index(3))
        operand1_qword = operand1.execute()

        operand2 = Instruction(self.get_instruction_at_index(4))
        operand2_qword = operand2.execute()

        bitset1, constants1 = self.get_last_qubitset(operand1.name, operand1_qword)
        bitset2, constants2 = self.get_last_qubitset(operand2.name, operand2_qword)

        sort = len(bitset1)
        result_qword = QWord(1, self.name)
        result_qword.create_state(Instruction.circuit, Instruction.current_n)
        # ancillas = 2 ancillas to add to each operand to perform substraction, sort to store the addition
        # (we actually need sort+1 to store addition, but we use result_qword to store the MSB).
        ancillas = result_qword.create_ancillas(Instruction.current_n, 2 + sort, Instruction.circuit)
        optimized_unsigned_ugt(bitset1, bitset2, result_qword, constants1, constants2, Instruction.circuit, ancillas,
                               Instruction.global_stack, Instruction.current_n)
        if QWord.are_all_constants(constants1) and QWord.are_all_constants(constants2):
            assert((get_decimal_representation(constants1) > get_decimal_representation(constants2))
                   == result_qword[Instruction.current_n][1][0])
        return result_qword


class Ugte(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        operand1 = Instruction(self.get_instruction_at_index(3))
        operand1_qword = operand1.execute()

        operand2 = Instruction(self.get_instruction_at_index(4))
        operand2_qword = operand2.execute()

        bitset1, constants1 = self.get_last_qubitset(operand1.name, operand1_qword)
        bitset2, constants2 = self.get_last_qubitset(operand2.name, operand2_qword)
        sort = len(bitset1)
        result_qword = QWord(1, self.name)
        result_qword.create_state(Instruction.circuit, Instruction.current_n, True)
        # ancillas =
        # LTE uses: 2 ancillas to add to each operand to perform substraction, sort to store the addition
        # (we actually need sort+1 to store addition, but we use result_qword to store the MSB).

        # 1 ancilla to save the result of LTE
        # 1 ancilla to save the result of EQ
        # EQ uses sort+1 ancillas
        ancillas = result_qword.create_ancillas(Instruction.current_n, 2 + sort + 2 + sort +1, Instruction.circuit)
        optimized_unsigned_ugte(bitset1, bitset2, result_qword, constants1, constants2, Instruction.circuit, ancillas,
                                Instruction.global_stack, Instruction.current_n)
        if QWord.are_all_constants(constants1) and QWord.are_all_constants(constants2):
            assert((get_decimal_representation(constants1) >= get_decimal_representation(constants2))
                   == result_qword[Instruction.current_n][1][0])
        return result_qword


class Udiv(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        operand1 = Instruction(self.get_instruction_at_index(3))
        operand1_qword = operand1.execute()

        operand2 = Instruction(self.get_instruction_at_index(4))
        operand2_qword = operand2.execute()

        bitset1, are_constants1 = self.get_last_qubitset(operand1.name, operand1_qword)
        bitset2, are_constants2 = self.get_last_qubitset(operand2.name, operand2_qword)
        assert len(bitset1) == len(bitset2)
        sort = self.get_sort().execute().size_in_bits
        if QWord.are_all_constants(are_constants1) and QWord.are_all_constants(are_constants2):
            bitset1_in_decimal = get_decimal_representation(are_constants1)
            bitset2_in_decimal = get_decimal_representation(are_constants2)
            result_in_decimal = bitset1_in_decimal // bitset2_in_decimal

            result_in_binary = get_bit_repr_of_number(result_in_decimal, len(bitset1))
            result_qword = QWord(sort, self.name)
            result_bits, result_consts = result_qword.create_state(Instruction.circuit, Instruction.current_n, True)

            for (index, res) in enumerate(result_in_binary):
                assert (result_consts[index] == 0)
                if res == 1:
                    Instruction.circuit.x(result_bits[index])
                    Instruction.global_stack.push(
                        Element(GATE_TYPE, X, [], result_bits[index]))
                    result_consts[index] = 1
            return result_qword
        raise Exception("not implemented")


class Urem(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        operand1 = Instruction(self.get_instruction_at_index(3))
        operand1_qword = operand1.execute()

        operand2 = Instruction(self.get_instruction_at_index(4))
        operand2_qword = operand2.execute()

        bitset1, are_constants1 = self.get_last_qubitset(operand1.name, operand1_qword)
        bitset2, are_constants2 = self.get_last_qubitset(operand2.name, operand2_qword)
        assert len(bitset1) == len(bitset2)
        sort = self.get_sort().execute().size_in_bits
        if QWord.are_all_constants(are_constants1) and QWord.are_all_constants(are_constants2):
            bitset1_in_decimal = get_decimal_representation(are_constants1)
            bitset2_in_decimal = get_decimal_representation(are_constants2)
            result_in_decimal = bitset1_in_decimal % bitset2_in_decimal

            result_in_binary = get_bit_repr_of_number(result_in_decimal, len(bitset1))
            result_qword = QWord(sort, self.name)
            result_bits, result_consts = result_qword.create_state(Instruction.circuit, Instruction.current_n, True)

            for (index, res) in enumerate(result_in_binary):
                assert (result_consts[index] == 0)
                if res == 1:
                    Instruction.circuit.x(result_bits[index])
                    Instruction.global_stack.push(
                        Element(GATE_TYPE, X, [], result_bits[index]))
                    result_consts[index] = 1
            return result_qword
        raise Exception("not implemented")


class Read(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        raise Exception("Not implemented")


class Bad(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> Optional[QWord]:
        bad_state = Instruction(self.get_instruction_at_index(2))
        bad_state_qword = bad_state.execute()
        bad_state_qubits, are_constants = self.get_last_qubitset(bad_state.name, bad_state_qword)
        assert bad_state_qword.size_in_bits == 1
        # Instruction.qubits_to_fix[bad_state_qubits[0]] = 1  # make the bad state happen
        qword_result = QWord(1)
        qword_result.append_state(bad_state_qubits, are_constants, Instruction.current_n)
        assert (len(are_constants) == 1)
        if are_constants[0] == -1:
            # only care if this bad state does not evaluates no a concrete value
            Instruction.bad_states.append(bad_state_qubits[0])
            Instruction.bad_states_to_line_no[bad_state_qubits[0]] = self.id
        else:
            if are_constants[0] == 1:
                print("true bad state found:", self.name)
        return qword_result


class Slice(Instruction):
    def __init__(self, instruction):
        super().__init__(instruction)

    def execute(self) -> QWord:
        sort = self.get_sort().execute().size_in_bits

        operand = Instruction(self.get_instruction_at_index(3))
        qword = operand.execute()
        qubitset, are_constants = self.get_last_qubitset(operand.name, qword)

        bottom = int(self.instruction[5])
        top = int(self.instruction[4])

        result_qubits = qubitset[bottom:top + 1]

        assert len(result_qubits) == (top - bottom) + 1
        assert (len(result_qubits) == sort)
        result_qword = QWord(sort, self.name)
        result_qword.append_state(result_qubits, are_constants[bottom:top + 1], Instruction.current_n)

        return result_qword
