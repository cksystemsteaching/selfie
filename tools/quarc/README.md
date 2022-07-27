# QUARC

QUBOT is a bounded model checker and a symbolic execution engine. It generates a Quantum Circuit in polynomic time from a given BTOR2 file and a given number of timesteps *n*.

The purpose of QUARC is to build an oracle than can be used in Grover's Algorithm to search for inputs that cause bad states.

## Usage
```` Python
from btor2QC import BTor2QC
from check_inputs import check_input # used only for debugging purposes

n = 21
parser = BTor2QC(n) # creates a btor2 file parser of 21 timesteps
quantum_circuit, result_bad_states = parser.parse_file(a_btor2_file, "output.qasm", is_selfie_file=True, generate_with_grover=False)

assert (len(result_bad_states) == 1) # this is a quantum register that represents the output of the circuit. 
# debug generated circuit
circuit_queue = get_circuit_queue(Instruction.global_stack)
for i in range(0, 256): # test ascii decimal values that fit in 1 byte
    circuit_output, bad_states = check_input(n, circuit_queue, i, result_bad_states)
    print(f"input {i} makes the circuit output {circuit_output}. {bad_states} happen")

````

## Prerequisites 
python >= 3.6


## Installation
Install required libraries (a virtual environment is recommended):

```bash
pip install -r requirements.txt
```