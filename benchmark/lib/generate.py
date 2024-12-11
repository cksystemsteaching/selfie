from .checks import execute
from .print import custom_exit
from .model_config_parser import ModelConfig, ModelConfigParser
import lib.config as cfg

import shutil
from queue import Queue


def create_model(source_file: str, model_type: str, output: str = ""):
    """
    Generates a model from a provided source file.

    Process of generation differs based on a language used (C* is compiled by Rotor itelf).
    Other languages need to be compiled to RISC-V machine code before model can be generated.
 
    Returns:
    str: path of generated model
    """
    model_config = ModelConfigParser(source_file, model_type, output).get_config()

    print(f"Generating model from the source: {model_config.source_file}")
    if not model_config.compilation_command:
        model = CStarSourceProcessor(model_config).generate_model()
    else:
        model = GenericSourceProcessor(model_config).generate_model()

    print(f"Generated model: {model_config.output}")
    return model


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

    def compile_source(self):
        """
        Compiles source into RISC-V machine code using compiler defined in config.
        Invokes Rotor using command defined in config.

        Returns:
        Path: path of generated output
        """
        self.compiled_source = self.model_config.source_file.with_suffix(".out")

        returncode, output = execute(
            self.model_config.compilation_command.format(
                source_file=self.model_config.source_file,
                output_machine_code=self.compiled_source
            )
        )

    def generate_model(self):
        self.compile_source()
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

    q = Queue(maxsize=0)
    q.put((cfg.config["models"], []))

    while not q.empty():
        curr_val = q.get()
        for key, value in curr_val[0].items():
            if isinstance(value, dict):
                q.put((value, curr_val[1] + [key]))
            else:
                if key == 'command':
                    # Provide a model type based on config file structure
                    model_type = "-".join(curr_val[1])
                    # Generate output directory based on config file structure and base models directory
                    output_dir = f"{cfg.models_dir}" + "/" + "/".join(curr_val[1])

                    files = [file for file in cfg.examples_dir.iterdir()]
                    for file in files:
                        if file.suffix != ".c":
                            continue
                        output = output_dir + "/" + file.stem + "." + curr_val[1][-1]
                        create_model(file, model_type, output)
