"""
User-facing interface for model specifications
- Model type definitions from config.yml
- Model type resolution

Key Components:
1. ModelType: User-facing interface for model specifications
2. get_all_model_types(): Discovers available model types
"""

from lib.model_config_parser import ModelConfigParser
from lib.exceptions import ParsingError, ConfigFormatError
import lib.config as cfg

from queue import Queue
from typing import List, Dict, Any

import logging


logger = logging.getLogger("bt.model_type")


class ModelType:
    """Represents a configured model type with its generation commands."""
    def __init__(self, model_type: str):
        self.name = model_type
        self.parser = ModelConfigParser(self.name)

    def get_bases(self):
        return self.parser.get_bases()
    
    def get_format(self):
        return self.parser.parse_format()

    def get_compile_cmd(self):
        return self.parser.parse_compile_cmd()

    def get_model_generation_cmd(self):
        return self.parser.parse_model_generation_cmd()

    def get_default_output_path(self):
        return self.parser.parse_default_output_path()


from lib.model_type import ModelType


def get_all_model_types(path_base: str = "") -> List[ModelType]:
    """
    Traverse the nested 'models' dictionary under cfg.config, drilling down
    according to a dash-delimited path (e.g., "starc-64bit-riscv"). Collect
    all model types for which a 'command' key is found.

    For example, if path_str is "starc-64bit", we go to:
        cfg.config["model_types"]["starc"]["64bit"]
    and then search every sub-dictionary below it for 'command'.

    Args:
        path_str (str): A dash-delimited path specifying a nested location
                        in cfg.config["model_types"]. If empty, we stay at the
                        top level (i.e., "model_types").

    Returns:
        List[str]: A list of model types. Each entry is a dash-delimited path
                   of keys (e.g., "riscv-btor2") leading to a 'command' node.
                   Returns an empty list if the specified path does not exist
                   or if no 'command' keys are found.
    """
    model_types: List[str] = []

    # Start at the top-level "models" dictionary. Use .get() to avoid KeyError
    # if "models" is missing; default to an empty dict in that case.
    models_dict: Dict[str, Any] = cfg.config.get("model_types", {})

    # Only split path_str if it's non-empty; otherwise, remain at the top level.
    path_segments = path_base.split("-") if path_base else []
    # Special keyword all - takes in all models
    if path_base == "all":
        path_segments = []

    # Drill down into the nested dictionary according to path_segments.
    current_node: Dict[str, Any] = models_dict
    for segment in path_segments:
        # Try to drill down
        if segment in current_node and isinstance(current_node[segment], dict):
            current_node = current_node[segment]
        else:
            logger.warning("Unable to parse passed model type...")
            raise ParsingError("model type", path_base, segment)

    # Use a queue to traverse the dictionary (BFS) below our current_node.
    queue = Queue()
    queue.put((current_node, []))  # (dict_node, path_keys_so_far)

    while not queue.empty():
        dict_node, path_keys = queue.get()

        if not isinstance(dict_node, dict) or is_dict_of_strings(dict_node):
            if path_keys:
                if path_base == "all":
                    model_type = f"{'-'.join(path_keys)}"
                else:
                    model_type = f"{path_base}-{'-'.join(path_keys)}"

            else:
                model_type = path_base

            model_types.append(model_type)

        else:
            for key, value in dict_node.items():
                # If it's another dict, enqueue it for further exploration
                if key != "compilation":
                    queue.put((value, path_keys + [key]))
    return list(map(lambda model: ModelType(model), model_types))


def is_dict_of_strings(value):
    if not isinstance(value, dict):
        return False
    return all(isinstance(k, str) and isinstance(v, str) for k, v in value.items())
