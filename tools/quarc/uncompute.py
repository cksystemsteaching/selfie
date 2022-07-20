from typing import List, Any, Optional
from qiskit import QuantumCircuit
from copy import deepcopy
from collections import deque

from qiskit.circuit.library import MCXGate

CHECKPOINT_TYPE = 0
GATE_TYPE = 1

X = "X"
CX = "CX"
MCX = "MCX"
CCX = "CCX"


class Element:
    element_type: int
    gate_name: str
    controls: List[Any]
    target: Any
    mcx_gate_index:int = 0

    def __init__(self, element_type, gate_name, controls, target):
        self.element_type = element_type
        self.gate_name = gate_name
        self.operands = controls[:]
        self.target = target

    @staticmethod
    def get_mcx_gate_index() -> int:
        Element.mcx_gate_index +=1
        return Element.mcx_gate_index

    def apply(self, circuit: QuantumCircuit):
        if type == CHECKPOINT_TYPE:
            return False
        else:
            assert(self.target is not None)
            if self.gate_name == X:
                assert(len(self.operands) == 0)
                circuit.x(self.target)
            elif self.gate_name == CX:
                assert(len(self.operands) == 1)
                circuit.cx(self.operands[0], self.target)
            elif self.gate_name == CCX:
                assert(len(self.operands) == 2)
                circuit.ccx(self.operands[0], self.operands[1], self.target)
            elif self.gate_name == MCX:
                # control_qubits = deepcopy(self.operands)
                #
                # gate=MCXGate(len(self.operands))
                # control_qubits.append(self.target)
                circuit.mcx(self.operands, self.target)
            else:
                raise Exception(f"Invalid stack element with gate {self.gate_name}")
        return True


class Queue:
    data_structure: deque
    size: int
    def __init__(self):
        self.data_structure = deque()
        self.size = 0

    def push(self, element: Element):
        self.data_structure.append(element)
        self.size += 1

    def is_empty(self):
        return self.size == 0

    def pop(self):
        if self.size == 0:
            return None
        self.size -=1
        return self.data_structure.popleft()


class Stack:
    data_structure: deque
    size: int

    def __init__(self):
        self.data_structure = deque()
        self.size = 0

    def push(self, element: Element) -> None:
        self.data_structure.append(element)
        self.size += 1

    def is_empty(self) -> int:
        return self.size == 0

    def pop(self) -> Optional[Element]:
        if self.size == 0:
            return None
        self.size -= 1
        return self.data_structure.pop()



def apply_and_reverse_stack(stack: Stack, circuit: QuantumCircuit):

    initial_size = stack.size
    temp_queue = Queue()

    while not stack.is_empty():
        element: Element = stack.pop()
        element.apply(circuit)
        temp_queue.push(element)

    while not temp_queue.is_empty():
        stack.push(temp_queue.pop())

    assert(stack.size == initial_size)

def get_circuit_queue(stack: Stack) -> Queue:

    result = Queue()
    result.data_structure.appendleft(Element(CHECKPOINT_TYPE, "", [], None))
    while not stack.is_empty():
        element = stack.pop()
        assert(element != None)
        result.data_structure.appendleft(element)
        result.size += 1
    return result