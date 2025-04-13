from pathlib import Path
import yaml

script_dir = Path(__file__).resolve().parent.parent
project_root = script_dir.parent

#Load the configuration file
config_file = script_dir / "config.yml"
with open(config_file, "r") as file:
    config = yaml.safe_load(file)

model_builder_path = Path(project_root / config["model_builder_path"])
models_dir = Path(project_root / config["models_dir"])
examples_dir = Path(project_root / config["examples_dir"])
verbose = False

RED = "\033[91m"
RESET = "\033[0m"

PIPE = -1
STDOUT = -2
DEVNULL = -3

# Define exit error codes
EXIT_SUCCESS = 0
EXIT_MODEL_GENERATION_ERROR = 2
EXIT_TOOL_NOT_FOUND = 3
EXIT_DIRECTORY_NOT_FOUND = 4
EXIT_TIMEOUT_ERROR = 5
