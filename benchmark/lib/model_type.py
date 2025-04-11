import lib.config as cfg
from lib.exceptions import ParsingError

from queue import Queue
from typing import List, Dict, Any
from pathlib import Path

import logging
logger = logging.getLogger("bt.model_type")
class ModelType:
    def __init__(self, model_base: str):
        self.model_base = model_base
        self.model_type_bases = self.model_base.split("-")
        self.parser = ModelConfigParser(self.model_type_bases)
    
    def get_model_type_bases(self):
        return self.model_type_bases
    
    def get_model_output_spec(self):
        """
        Return a transformed model base that is appropriate to use
        as a part of output file name to further specify it.
        This is used if no specific output name is passed as an argument.
        """
        return "_" + self.model_type_bases[:-1].join("_") + "." + self.get_format()
    
    def get_format(self):
        return self.parser.parse_format()

    def get_compile_cmd(self):
        return self.parser.parse_compile_cmd()
    
    def get_model_generation_cmd(self):
        return self.parser.parse_model_generation_cmd()
    
    def get_default_output_path(self):
        return self.parser.parse_default_output_path()

class ModelConfigParser:
    def __init__(self, model_type_bases: List[str]):
        self.top_level = cfg.config["models"]
        self.model_type_bases = model_type_bases
        self.check()

    def check(self):
        current_level = self.top_level

        for level in self.model_type_bases:
            if level in current_level:
                current_level = current_level[level]
            else: 
                raise ParsingError(self.model_base, level)

        # Check if type has specified Rotor command in config file
        required_values = ['command']
        for value in required_values:
            if value not in current_level:
                raise ValueError(f"{value} not present/or at the wrong place in specified model type")
        
        allowed_formats = cfg.config["allowed_formats"]
        if self.parse_format() not in allowed_formats:
            raise ValueError(f"{self.parse_format()} is not an allowed format")
    
    def parse_format(self):
        return self.model_type_bases[-1]
    
    def parse_model_generation_cmd(self):
        current_level = self.top_level

        for level in self.model_type_bases:
            current_level = current_level[level]
        
        return current_level["command"]
    
    def parse_compile_cmd(self):
        """
        That we can drill down with provided bases does not have to be checked since it was already checked in constructor.
        """
        current_level = self.top_level

        for level in self.model_type_bases:
            if 'compilation' in current_level:
                return current_level["compilation"]
            current_level = current_level[level]
        
        return ""      


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

    #Drill down into the nested dictionary according to path_segments.
    current_node: Dict[str, Any] = models_dict
    for segment in path_segments:
        # Try to drill down
        if segment in current_node and isinstance(current_node[segment], dict):
            current_node = current_node[segment]
        else: 
            current_node = [None]

    # Use a queue to traverse the dictionary (BFS) below our current_node.
    queue = Queue()
    queue.put((current_node, []))  # (dict_node, path_keys_so_far)

    while not queue.empty():
        dict_node, path_keys = queue.get()

        if not isinstance(dict_node,dict) or is_dict_of_strings(dict_node):
            if path_keys:
                model_type = f"{path_base}-{'-'.join(path_keys)}"
            else:
                model_type = path_base

            model_types.append(model_type)

        else:
            for key, value in dict_node.items():
                # If it's another dict, enqueue it for further exploration
                queue.put((value, path_keys + [key]))
            
    logger.verbose_info(f"All parsed model types:{model_types}")
    return list(map(lambda model: ModelType(model),model_types))

def is_dict_of_strings(value):
    if not isinstance(value, dict):
        return False
    return all(isinstance(k, str) and isinstance(v, str) for k, v in value.items())