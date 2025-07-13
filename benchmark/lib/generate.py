"""
Core model generation pipeline for BT. Handles:
- Loading existing models (SMT2/BTOR2)
- Generating new models from C/C* sources
- Compilation pipeline for non-C* languages

The workflow:
1. `load_models()` - For benchmarking existing models
2. `create_models()` - For generating new models from source files
3. Processor classes - Handle format-specific generation (C* vs compiled languages)
"""

from lib.utils import execute, is_tool_available, check_model_builder
from lib.model_generation_config import ModelGenerationConfig, ModelLoadConfig
from lib.model_type import ModelType
from lib.paths import SourcePath, OutputPath, LoadSourcePath
from lib.model import model_factory
from lib.exceptions import ParsingError
import lib.config as cfg

from typing import List
import logging

logger = logging.getLogger("bt.generate")


def load_models(source: LoadSourcePath) -> list:
    """
    Loads already generated models, so benchmark is possible. Handles both single files and directories.

    Args:
        source: Source file or directory containing models
        output: Output path (file or directory)
    """
    if source.is_dir():
        models = []
        for file in source.iterdir():
            if file.suffix.lstrip(".").lower() in cfg.config["allowed_formats"]:
                models.extend(load_models(LoadSourcePath(file)))
        return models

    models = []
    logger.info(f"Loading model: {source}")
    try:
        model = model_factory(ModelLoadConfig(source))
        models.append(model)
    except ParsingError as e:
        logger.warning(f"Skipping invalid model {source.path}...")

    return models


def create_models(source: SourcePath, model_types: List[ModelType], output: OutputPath) -> list:
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
                models.extend(create_models(SourcePath(file), model_types, output))
        return models
    else:
        logger.info(f"Generating model from source: {source}")
        models = []

        for model_type in model_types:
            model_config = ModelGenerationConfig(source, model_type, output)

            model_generation_success = False
            if not model_config.compilation_cmd:
                model_generation_success = CStarSourceProcessor(
                    model_config
                ).generate_model()
            else:
                model_generation_success = GenericSourceProcessor(
                    model_config
                ).generate_model()

            if model_generation_success:
                logger.info(f"Generated model: {model_config.output_path}")
                models.append(model_factory(model_config))
            else:
                logger.warning(f"Failed to generate: {model_config.output_path}")

        return models


class BaseSourceProcessor:
    def __init__(self, model_config: ModelGenerationConfig):
        self.model_config = model_config

    def generate_model(self):
        raise NotImplementedError("Abstract class")


class CStarSourceProcessor(BaseSourceProcessor):
    """Direct RISC-V generation using Selfie/Rotor (no compilation needed)."""
    def __init__(self, model_config: ModelGenerationConfig):
        super().__init__(model_config)

    def generate_model(self):
        """
        Invokes Rotor and return generated output

        Returns:
        Path: path of generated output
        """
        check_model_builder()
        # Selfie generates binary file as well, but that is not needed
        returncode, output = execute(
            self.model_config.model_generation_cmd.format(
                rotor=cfg.model_builder_path,
                source_file=self.model_config.source_path,
                output=self.model_config.output_path,
            )
        )
        if returncode != 0:
            logger.warning(
                f"Model failed to generate. Model builder povided this output: {output}"
            )
            return False

        return True


class GenericSourceProcessor(BaseSourceProcessor):
    """Handles compiled languages via GCC -> RISC-V -> Rotor pipeline.
    
    Additional steps:
    1. check_compiler() - Verify toolchain availability
    2. compile_source() - Compile to RISC-V machine code
    """
    def __init__(self, model_config: ModelGenerationConfig):
        super().__init__(model_config)

    def check_compiler(self) -> bool:
        self.compiler = self.model_config.compilation_cmd.split()[0]
        return is_tool_available(self.compiler)

    def compile_source(self) -> bool:
        """
        Compiles source into RISC-V machine code using compiler defined in config.
        Invokes Rotor using command defined in config.

        Returns:
        Path: path of generated output
        """
        logger.verbose_info(f"Compiling source {self.model_config.source_path}")
        self.compiled_source = self.model_config.source_path.with_suffix(".out")

        if not self.check_compiler():
            return False

        returncode, output = execute(
            self.model_config.compilation_command.format(
                source_file=self.model_config.source_path,
                output_machine_code=self.compiled_source,
            )
        )
        if returncode != 0:
            logger.error(
                f"Source {self.model_config.source_path} not correctly compiled. Compiler provided following output: {output}"
            )
            return False

        return True

    def generate_model(self):
        if not self.compile_source():
            logger.warning(f"Compiler {self.compiler} not available.")
            return False

        check_model_builder()
        returncode, output = execute(
            self.model_config.model_generation_command.format(
                rotor=cfg.model_builder_path,
                source_file=self.compiled_source,
                output=self.model_config.output_path,
            )
        )
        self.compiled_source.unlink()
        if returncode != 0:
            logger.warning(
                f"Model failed to generate. Model builder povided this output: {output}"
            )
            return False

        return True
