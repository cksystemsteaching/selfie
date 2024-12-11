from dataclasses import dataclass
from .exceptions import ParsingError
import lib.config as cfg

import os
from pathlib import Path


@dataclass
class ModelConfig:
    source_file: Path
    output: Path
    compilation_command: str = ""
    model_generation_command: str = ""


class ModelConfigParser:
    def __init__(self, source_file: str, model_type: str, output: str = ""):
        self.source_file = Path(source_file)
        self.compilation_command = ""
        self.output = output
        self.parse_config(model_type)

    def parse_config(self, model_type):
        parsed_models = model_type.split("-")
        current_level = cfg.config["models"]
        for level in parsed_models:
            if level in current_level:
                if 'compilation' in current_level:
                    self.compilation_command = current_level["compilation"]
                current_level = current_level[level]
            else:
                raise ParsingError(model_type, level)

        # extension should always be the last level in the config
        self.extension = parsed_models[-1]
        self.output = self.get_output_file_path(current_level)
        self.model_generation_command = current_level["command"]

        if not self.model_generation_command or not self.output:
            raise ParsingError(model_type, level)

    def get_output_file_path(self, model):
        if self.output != "":
            parent_directories = Path(self.output).parent
            if not parent_directories.exists():
                parent_directories.mkdir(parents=True)
            return self.output

        output_dir = Path(cfg.models_dir / model.get("output", None))

        if not output_dir.exists():
            self.output_dir.mkdir(parents=True)

        output = output_dir / self.source_file.with_suffix("." + self.extension).name
        return output

    def get_config(self) -> ModelConfig:
        return ModelConfig(
            self.source_file,
            self.output,
            self.compilation_command,
            self.model_generation_command,
        )

    def log(self):
        print("Current config has been parsed:")
        print(f"source_file: {self.source_file}")
        print(f"output: {self.output}")
        print(f"compilation_command: {self.compilation_command}")
        print(f"model_generation_command: {self.model_generation_command}")
        print("--------------------------------------------------------")
