
# Usage
```` Python
from btor2bqm import BTor2BQM
from bqm_input_checker import InputChecker # used only for debugging purposes

parser = BTor2BQM(21) # creates a btor2 file parser of 21 timesteps
bqm = parser.parse_file(f"./btor2files/a_btor2_file.btor2",f"./output_dir_path/", input_nid=81)

# debug generated function
for i in range(0, 256): # test ascii decimal values that fit in 1 byte
    energy, error_states = InputChecker.run_checker(f"./output_dir_path/", i)
    print(f"{i}: ",energy, error_states)

# run an exact solver (with more than 21 variables it is really slow)
result_sampleset = parser.run_exact_solver(f"./btor2files/a_btor2_file.btor2",f"./output_dir_path/", input_nid=81)

# run DWave's quantum annealer
result_sampleset = parser.run_quantum_solver(f"./btor2files/a_btor2_file.btor2",f"./output_dir_path/", input_nid=81)

````

If the model is still in memory built by calling one of the three methods of `parser`,
you can use the method `BTor2BQM.get_variable_value(some_nid, timestep_t, result_sampleset)` to get any **nid** 
value at any timestep.


# Prerequisites 
python >= 3.6


# Installation
Install required libraries (a virtual environment is recommended):

```bash
pip install -r requirements.txt
```

If you want to submit problems to DWave's quantum computer you should setup your configurations files after installing the libraries.
Follow the [setup guide of Dwave](https://docs.ocean.dwavesys.com/en/latest/overview/install.html#set-up-your-environment).

The file `quantum_computer_tests/pure_qa` contains further examples of how to use run a BQM in DWave's annealer.


