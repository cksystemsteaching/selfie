from pathlib import Path
import yaml

script_dir = Path(__file__).resolve().parent.parent
project_root = script_dir.parent

# Load the configuration file
config_file = script_dir / "config.yml"
with open(config_file, "r") as file:
    config = yaml.safe_load(file)

model_builder_path = Path(project_root / config["model_builder_path"])
verbose = False