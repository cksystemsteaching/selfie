import sys
from utils import *
from instructions import Instruction
from settings import *
from qiskit import QuantumRegister, ClassicalRegister
from math import sqrt, ceil
from uncompute import *

n = int(sys.argv[1])
input_file = sys.argv[2]
output_file = sys.argv[3]
generate_with_grover = int(sys.argv[4])

current_settings = get_btor2_settings(input_file)
Instruction.all_instructions = read_file(input_file, modify_memory_sort=True, setting=current_settings)

Instruction.ZERO_CONST = QuantumRegister(1, name="zeroq")
Instruction.ONE_CONST = QuantumRegister(1, name="oneq")
Instruction.with_grover = generate_with_grover
# # Instruction.circuit.add_register(Instruction.ZERO_CONST)
# # Instruction.circuit.add_register(Instruction.ONE_CONST)
# # Instruction.circuit.x(Instruction.ONE_CONST)
# Instruction.initialize_memory_addresses()
for i in range(1, n+1):
    Instruction.current_n = i

    for instruction in Instruction.all_instructions.values():
        if instruction[1] == INIT and i == 1:
            Instruction(instruction).execute()

        elif instruction[1] == NEXT or instruction[1] == BAD:
            Instruction(instruction).execute()

result_bad_states = Instruction.or_bad_states()
assert(len(result_bad_states) == 1)


if generate_with_grover:

    input_qubits = Instruction.get_input_qubits()
    # dumb = QuantumRegister(1)
    # Instruction.circuit.add_register(dumb)
    # Instruction.circuit.h(dumb)
    # print("len input", len(input_qubits))
    # temp = input_qubits[:]
    # temp.extend(dumb[:])
    # input_qubits = QuantumRegister(bits=temp)
    # print("len input",len(input_qubits))

    gout = QuantumRegister(1, "gout")
    assert(len(gout) == 1)

    Instruction.circuit.add_register(gout)

    # initialize gout in |->
    Instruction.circuit.x(gout)
    #Instruction.circuit.h(gout)

    # mark answers
    Instruction.circuit.barrier()
    Instruction.circuit.cz(result_bad_states[0], gout[0])
    Instruction.circuit.barrier()
    # uncompute
    apply_and_reverse_stack(Instruction.global_stack, Instruction.circuit)

    Instruction.circuit.barrier()
    apply_amplitude_amplification(input_qubits, Instruction.circuit)

    Instruction.circuit.barrier()
    iterations = int(sqrt(2**len(input_qubits)))

    # marked states undo:
    # Instruction.circuit.h(gout)

    print("Grover will need ",iterations, "iterations.")

    for i in range(iterations-2):
        # compute
        apply_and_reverse_stack(Instruction.global_stack, Instruction.circuit)

        Instruction.circuit.barrier()
        # mark answers
        Instruction.circuit.cz(result_bad_states[0], gout[0])
        Instruction.circuit.barrier()
        # uncompute
        apply_and_reverse_stack(Instruction.global_stack, Instruction.circuit)
        Instruction.circuit.barrier()

        apply_amplitude_amplification(input_qubits, Instruction.circuit)
        Instruction.circuit.barrier()


    classical_register = ClassicalRegister(len(input_qubits))
    Instruction.circuit.add_register(classical_register)

    Instruction.circuit.measure(input_qubits, classical_register)

Instruction.circuit.qasm(filename=output_file)

