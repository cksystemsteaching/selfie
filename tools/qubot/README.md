
# Usage
```` Python
from btor2bqm import BTor2BQM
from bqm_input_checker import InputChecker

parser = BTor2BQM(21) # creates a btor2 file parser of 21 timesteps
parser.parse_file(f"./btor2files/a_btor2_file.btor2",f"./output_dir_path/")

for i in range(0, 256):
    energy, error_states = InputChecker.run_checker(f"./output_dir_path/", i)
    print(f"{i}: ",energy, error_states)

````

# Prerequisites 
python >= 3.6


# Instalation
Install required libraries (a virtual environment is recommended):

```bash
pip install -r requirements.txt
```

If you want to submit problems to DWave's quantum computer you should setup your configurations files after installing the libraries.
Follow the [setup guide of Dwave](https://docs.ocean.dwavesys.com/en/latest/overview/install.html#set-up-your-environment).

The file `quantum_computer_tests/pure_qa` contains further examples of how to use run a BQM in DWave's annealer.


