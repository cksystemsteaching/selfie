from instructions import Instruction
from settings import *
from utils import *
from qiskit import ClassicalRegister
from uncompute import *
from math import sqrt


class BTor2QC:
    """
    interface to convert a btor2 file into a binary quadratic model
    """

    def __init__(self, n: int):
        """
        :param n: number of state transitions
        """
        self.n = n
        if n <= 0:
            raise Exception("number of instructions to execute cannot be less than 1.")

    def parse_file(self, input_file, output_file=None, is_selfie_file=True, generate_with_grover=False) -> \
            (QuantumCircuit, QuantumRegister):
        current_settings = get_btor2_settings(input_file)
        Instruction.all_instructions = read_file(input_file, modify_memory_sort=is_selfie_file,
                                                 setting=current_settings)
        for i in range(1, self.n + 1):
            Instruction.current_n = i

            for instruction in Instruction.all_instructions.values():
                if instruction[1] == INIT and i == 1:
                    Instruction(instruction).execute()

                elif instruction[1] == NEXT or instruction[1] == BAD:
                    Instruction(instruction).execute()

        result_bad_states = Instruction.or_bad_states()
        assert (len(result_bad_states) == 1)

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
            assert (len(gout) == 1)

            Instruction.circuit.add_register(gout)

            # initialize gout in |->
            Instruction.circuit.x(gout)
            # Instruction.circuit.h(gout)

            # mark answers
            Instruction.circuit.barrier()
            Instruction.circuit.cz(result_bad_states[0], gout[0])
            Instruction.circuit.barrier()
            # uncompute
            apply_and_reverse_stack(Instruction.global_stack, Instruction.circuit)

            Instruction.circuit.barrier()
            apply_amplitude_amplification(input_qubits, Instruction.circuit)

            Instruction.circuit.barrier()
            iterations = int(sqrt(2 ** len(input_qubits)))

            # marked states undo:
            # Instruction.circuit.h(gout)

            print("Grover will need ", iterations, "iterations.")

            for i in range(iterations - 2):
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

        if output_file is not None:
            Instruction.circuit.qasm(filename=output_file)
        return Instruction.circuit, result_bad_states
