from dataclasses import dataclass
from .exceptions import ParsingError
from .model_type import ModelType
from .paths import SourcePath, OutputPath
import lib.config as cfg

import os
from pathlib import Path

    

class ModelGenerationConfig:
    def __init__(self, source_path: SourcePath, model_type: ModelType, output_path: OutputPath):
        self.source_path = source_path
        self.compilation_cmd = model_type.get_compile_cmd()
        self.model_generation_cmd = model_type.get_model_generation_cmd()
        self.output = output_path.try_build_output_path(generate_output_name(source_path, model_type), model_type.get_format())

def generate_output_name(source_path: SourcePath, model_type: ModelType):
    filename = f"{source_path.path.stem}_{'_'.join(model_type.model_type_bases[:-1])}"
    return filename
