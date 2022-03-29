from typing import List, Optional, Dict
from settings import *
from tools import *


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

    def __init__(self, size_in_bits: int = 64, name: str = ""):
        """
        @param size_in_bits: this is the number of bits that this 'piece of memory occupies'. Default is WORD_SIZE, a variable
        declared at settings.py
        :rtype: object
        """

        self.states = {}  # saves the transformations of qubits. Each element of this array is an array with
        # size_in_bits elements. These elements are the names of the qubits that represent
        # this variable in a given transformation.
        self.size_in_bits = size_in_bits
        self.name = name
        self.last_n = -1

    def __len__(self):
        return len(self.states)

    def __getitem__(self, i):
        return self.states[i]

    def __repr__(self):
        return self.states.__str__()

    def append_state(self, state: List[int], n: int) -> None:
        self.last_n = max(n, self.last_n)
        self.states[n] = state

    def create_state(self, bqm: dimod.BinaryQuadraticModel, n: int) -> List[int]:
        """
        creates a state with qubits in perfect superposition.

        @param bqm: binary quadratic model to update.
        @return: the new state created
        """
        self.last_n = max(n, self.last_n)

        state_index = len(self)  # we need index of the timestep we are creating to name the newly
        # created qubits
        qubits = [GlobalIndexer.get_name_index() for _ in range(self.size_in_bits)]
        for qubit in qubits:
            bqm.add_variable(qubit)
        self.append_state(qubits, n)
        return qubits

    @property
    def top(self) -> Optional[List[int]]:
        if self.states[self.last_n]:
            if len(self.states[self.last_n]) > 0:
                return self.states[self.last_n]
        assert False
