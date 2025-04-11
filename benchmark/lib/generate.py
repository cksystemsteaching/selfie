from .checks import execute, is_tool_available
from .print import custom_exit
from .model_generation_config import ModelGenerationConfig
from .model_type import get_all_model_types
from .paths import SourcePath, OutputPath
from .model import model_factory
import logging

import lib.config as cfg
from pathlib import Path

import shutil

log = logging.getLogger("bt.generate")

def create_models(source: SourcePath, model_type_base: str, output: OutputPath) -> list:
    """
    Generates models from source files. Handles both single files and directories.
    
    Args:
        source: Source file or directory containing source files
        model_type_base: Base model type identifier
        output: Output path (file or directory)
    
    Returns:
        List of paths to generated models
    """
    if source.is_dir():
        models = []
        for file in source.iterdir():
            if file.suffix.lower() in cfg.config["allowed_languages"]:
                models.extend(
                    create_models(SourcePath(file), model_type_base, output)
                )
        return models
    else:
        log.info(f"Generating model from source: {source}")
        model_types = get_all_model_types(model_type_base)
        models = []
        
        for model_type in model_types:
            model_config = ModelGenerationConfig(source, model_type, output)
            
            if not model_config.compilation_cmd:
                CStarSourceProcessor(model_config).generate_model()
            else:
                GenericSourceProcessor(model_config).generate_model()

            log.info(f"Generated model: {model_config.output_path}")
            models.append(model_factory(model_config))
        
        return models

class BaseSourceProcessor:
    def __init__(self, model_config: ModelGenerationConfig):
        self.model_config = model_config

    def generate_model(self):
        raise NotImplementedError("Abstract class")


class CStarSourceProcessor(BaseSourceProcessor):
    def __init__(self, model_config: ModelGenerationConfig):
        super().__init__(model_config)

    def generate_model(self):
        """
        Invokes Rotor and return generated output

        Returns:
        Path: path of generated output
        """
        # Selfie generates binary file as well, but that is not needed
        returncode, output = execute(
            self.model_config.model_generation_cmd.format(
                rotor=cfg.rotor_path,
                source_file=self.model_config.source_path,
                output=self.model_config.output_path
            )
        )
        if returncode != 0:
            custom_exit(output, cfg.EXIT_MODEL_GENERATION_ERROR)

        return self.model_config.output_path


class GenericSourceProcessor(BaseSourceProcessor):
    def __init__(self, model_config: ModelGenerationConfig):
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
        self.compiled_source = self.model_config.source_path.with_suffix(".out")

        if not self.check_compiler():
            return False

        returncode, output = execute(
            self.model_config.compilation_command.format(
                source_file=self.model_config.source_path,
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
                output=self.model_config.output_path
            )
        )
        self.compiled_source.unlink()
        if returncode != 0:
            custom_exit(output, cfg.EXIT_MODEL_GENERATION_ERROR)

        return self.model_config.output_path


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
            create_models(file, model, output)
