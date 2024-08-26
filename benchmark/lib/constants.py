from pathlib import Path

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


starc_64_riscv_path = Path(models_dir/"starc"/"64-bit"/"riscv")
starc_64_riscu_path = Path(models_dir/"starc"/"64-bit"/"riscu")
