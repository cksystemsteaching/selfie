from pathlib import Path

RED = "\033[91m"
RESET = "\033[0m"

PIPE = -1
STDOUT = -2
DEVNULL = -3

# Define exit error codes
EXIT_SUCCESS = 0
EXIT_MODEL_GENERATION_ERROR = 2
EXIT_TOOL_NOT_FOUND = 3

rotor_path = Path("../rotor")
examples_dir = Path("../examples/symbolic")
models_dir = Path("../models")


cstar_64_riscv_btor2_path = Path(models_dir/"starc"/"64-bit"/"riscv"/"btor2")
cstar_64_riscu_smt_path = Path(models_dir/"starc"/"64-bit"/"riscu"/"smt")
cstar_64_riscu_btor2_path = Path(models_dir/"starc"/"64-bit"/"riscu"/"btor2")
