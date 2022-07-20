from typing import List, Optional, Dict
from settings import *
from qiskit import QuantumCircuit, QuantumRegister
from utils import *


class QWord:
    """
    This class is a general abstraction of a piece of memory. This class group qubits to represent
    a variable/constant and change its value as required.
    """
    size_in_bits: int
    name: str
    states: Dict[int, List[int]]  # we don't use a vector cause we will create qwords whose first record is
    # not necessarily a first step
    last_n: int
    ancillas: Dict[int, QuantumRegister]

    def __init__(self, size_in_bits: int = 64, name: str = ""):
        """
        @param size_in_bits: this is the number of bits that this 'piece of memory occupies'. Default is WORD_SIZE, a variable
        declared at settings.py
        :rtype: object
        """

        self.states: Dict[int, (QuantumRegister, List[int])] = {}  # saves the transformations of qubits. Each element of this array is an array with
        # size_in_bits elements. These elements are the names of the qubits that represent
        # this variable in a given transformation.
        self.size_in_bits = size_in_bits
        self.name = name
        self.last_n = -1
        self.ancillas = {}

    def __len__(self):
        return len(self.states)

    def __getitem__(self, i):
        return self.states[i]

    def __repr__(self):
        return self.states.__str__()

    def append_state(self, state: QuantumRegister, constants:List[int], n: int) -> None:
        assert(len(state) == len(constants))
        if len(state) != self.size_in_bits:
            print(len(state), self.size_in_bits)
        assert(len(state) == self.size_in_bits)
        self.last_n = max(n, self.last_n)
        self.states[n] = (state, constants)

    def create_ancillas(self, n, size, circuit) -> QuantumRegister:
        self.ancillas[n] = QuantumRegister(size)
        circuit.add_register(self.ancillas[n])
        return self.ancillas[n]

    def create_state(self, circuit: QuantumCircuit, n: int, set_name=False) -> (QuantumRegister, List[int]):
        """
        creates a state with qubits in perfect superposition.

        @param circuit: binary quadratic model to update.
        @return: the new state created
        """
        # if not set_name:
        qubits = QuantumRegister(self.size_in_bits)
        # else:
        #     qubits = QuantumRegister(self.size_in_bits, self.name)
        constants = [0 for _ in range(self.size_in_bits)]
        circuit.add_register(qubits)
        self.append_state(qubits, constants, n)
        return qubits, constants

    @staticmethod
    def are_all_constants(constants: List[int]) -> bool:
        for c in constants:
            if c == -1:
                return False
        return True

    def get_word_value(self, n: int) -> int:
        _, word = self.states[n]
        return get_decimal_representation(word)

    @property
    def top(self) -> (QuantumRegister, List[int]):
        if self.states[self.last_n]:
            if len(self.states[self.last_n]) > 0:
                return self.states[self.last_n]
        assert False
