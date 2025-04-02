from .checks import execute, is_tool_available
from .print import custom_exit
from .model_config_parser import ModelConfig, ModelConfigParser
import lib.config as cfg
from pathlib import Path

import shutil
from queue import Queue
from typing import List, Dict, Any

def create_model(source_file: str, model_type_base: str, output: str = ""):
    """
    Generates a model from a provided source file.

    Process of generation differs based on a language used (C* is compiled by Rotor itelf).
    Other languages need to be compiled to RISC-V machine code before model can be generated.

    Returns:
    str: path of generated model
    """
    model_types = get_all_model_types(model_type_base)

    models = []
    for model_type in model_types:
        model_config = ModelConfigParser(source_file, model_type, output).get_config()

        print(f"Generating model from the source: {model_config.source_file}")
        if not model_config.compilation_command:
            model = CStarSourceProcessor(model_config).generate_model()
        else:
            model = GenericSourceProcessor(model_config).generate_model()

        print(f"Generated model: {model_config.output}")
        models.append(model)

    return models


def create_models_from_dir(source_dir: str, model_type: str, output: str = ""):
    """
    Create models from all `.c` files found in a specified directory.
    """
    print(f"Generating models from directory: {source_dir}")
    output_paths = []
    files = [file for file in Path(source_dir).iterdir()]
    for file in files:
        if file.suffix != ".c":
            continue
        output_paths.append(create_model(file.resolve(), model_type, output))

    return output_paths

class BaseSourceProcessor:
    def __init__(self, model_config: ModelConfig):
        self.model_config = model_config

    def generate_model(self):
        raise NotImplementedError("Abstract class")


class CStarSourceProcessor(BaseSourceProcessor):
    def __init__(self, model_config: ModelConfig):
        super().__init__(model_config)

    def generate_model(self):
        """
        Invokes Rotor and return generated output

        Returns:
        Path: path of generated output
        """
        # Selfie generates binary file as well, but that is not needed
        returncode, output = execute(
            self.model_config.model_generation_command.format(
                rotor=cfg.rotor_path,
                source_file=self.model_config.source_file,
                output=self.model_config.output
            )
        )
        if returncode != 0:
            custom_exit(output, cfg.EXIT_MODEL_GENERATION_ERROR)

        return self.model_config.output


class GenericSourceProcessor(BaseSourceProcessor):
    def __init__(self, model_config: ModelConfig):
        super().__init__(model_config)

    def check_compiler(self) -> bool:
        self.compiler = self.model_config.compilation_command.split()[0]
        return is_tool_available(self.compiler)

    def compile_source(self) -> bool:
        """
        Compiles source into RISC-V machine code using compiler defined in config.
        Invokes Rotor using command defined in config.

        Returns:
        Path: path of generated output
        """
        self.compiled_source = self.model_config.source_file.with_suffix(".out")

        if not self.check_compiler():
            return False

        returncode, output = execute(
            self.model_config.compilation_command.format(
                source_file=self.model_config.source_file,
                output_machine_code=self.compiled_source
            )
        )
        return True

    def generate_model(self):
        if not self.compile_source():
            print(f"Warning: Compiler {self.compiler} not available")
            return

        returncode, output = execute(
            self.model_config.model_generation_command.format(
                rotor=cfg.rotor_path,
                source_file=self.compiled_source,
                output=self.model_config.output
            )
        )
        self.compiled_source.unlink()
        if returncode != 0:
            custom_exit(output, cfg.EXIT_MODEL_GENERATION_ERROR)

        return self.model_config.output


def clean_examples() -> None:
    if cfg.models_dir.is_dir():
        shutil.rmtree(cfg.models_dir)


def generate_all_examples() -> None:
    """
    Examples directory is defined in config file.
    Clean previous generated examples, then recursively traverse examples sources (directory of examples defined in config file)
    and generates models defined in config file for each source inside this example directory. 
    Output directory is also specified by a config file.
    """
    clean_examples()
    models = get_all_model_types()

    for model in models:
        parts = model.split("-")
        # All but the last part
        model_name = "-".join(parts[:-1])

        # Just the last part
        model_suffix = parts[-1]

        files = [file for file in cfg.examples_dir.iterdir()]
        for file in files:
            if file.suffix != ".c":
                continue
            output_dir = Path(cfg.models_dir) / model
            output = output_dir / Path(file.stem + "-" + model_name + "." + model_suffix)
            print(f"Output: {output}")
            create_model(file, model, output)


def get_all_model_types(path_base: str = "") -> List[str]:
    """
    Traverse the nested 'models' dictionary under cfg.config, drilling down
    according to a dash-delimited path (e.g., "starc-64bit-riscv"). Collect
    all model types for which a 'command' key is found.

    For example, if path_str is "starc-64bit", we go to:
        cfg.config["models"]["starc"]["64bit"]
    and then search every sub-dictionary below it for 'command'.

    Args:
        path_str (str): A dash-delimited path specifying a nested location
                        in cfg.config["models"]. If empty, we stay at the
                        top level (i.e., "models").

    Returns:
        List[str]: A list of model types. Each entry is a dash-delimited path
                   of keys (e.g., "riscv-btor2") leading to a 'command' node.
                   Returns an empty list if the specified path does not exist
                   or if no 'command' keys are found.
    """
    model_types: List[str] = []

    # Start at the top-level "models" dictionary. Use .get() to avoid KeyError
    # if "models" is missing; default to an empty dict in that case.
    models_dict: Dict[str, Any] = cfg.config.get("models", {})

    # Only split path_str if it's non-empty; otherwise, remain at the top level.
    path_segments = path_base.split("-") if path_base else []

    # Safely drill down into the nested dictionary according to path_segments.
    current_node: Dict[str, Any] = models_dict
    for segment in path_segments:
        # Check that segment is a valid key and is still a dictionary
        if segment in current_node and isinstance(current_node[segment], dict):
            current_node = current_node[segment]
        else:
            # If the segment doesn't exist or isn't a dictionary, bail out.
            return []

    # Use a queue to traverse the dictionary (BFS) below our current_node.
    # We'll look for any sub-node containing a key "command".
    queue = Queue()
    queue.put((current_node, []))  # (dict_node, path_keys_so_far)

    while not queue.empty():
        dict_node, path_keys = queue.get()

        for key, value in dict_node.items():
            if isinstance(value, dict):
                # If it's another dict, enqueue it for further exploration
                queue.put((value, path_keys + [key]))
            else:
                # If it's not a dict, check if this key is "command"
                if key == "command":
                    # Build the dash-delimited path from path_keys
                    # (the last key is "command", so we omit it)
                    model_type = path_base + "-" + "-".join(path_keys)
                    model_types.append(model_type)

    return model_types
