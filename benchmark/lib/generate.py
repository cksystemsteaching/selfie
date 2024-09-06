from .checks import execute
from .print import custom_exit
from .exceptions import ParsingError
import lib.config as cfg

from pathlib import Path
import shutil

CSTAR_64_BIT_RISCU_BTOR = 1
CSTAR_64_BIT_RISCU_SMT = 2
CSTAR_64_BIT_RISCV_BTOR = 3
CSTAR_64_BIT_RISCV_SMT = 4

CSTAR_32_BIT_RISCU_BTOR = 5
CSTAR_32_BIT_RISCU_SMT = 6
CSTAR_32_BIT_RISCV_BTOR = 7
CSTAR_32_BIT_RISCV_SMT = 8


class ModelType:
    def __init__(self, source_file: Path, model_type: str, is_example: bool = False):
        self.source_file = source_file
        self.is_example = is_example
        self.parse_model_type(model_type)

    def parse_model_type(self, model_type: str):
        self.compilable = False
        parsed_models = model_type.split("-")
        current_model = cfg.config["models"]
        for level in parsed_models:
            if level in current_model:
                current_model = current_model[level]
                if 'compilation' in current_model:
                    self.compilable = True
                    self.compilation_command = current_model["compilation"]
            else:
                raise ParsingError(model_type, level)
        self.output = self.get_output_directory(current_model)
        self.command = current_model["command"].format(
            rotor=cfg.rotor_path,
            source_file=self.source_file,
            output=self.output
        )
        if not self.command or not self.output:
            raise ParsingError(model_type, level)

    def get_output_directory(self, model):
        if self.is_example:
            outdir = Path(cfg.models_dir / model.get("example_output", None))
        else:
            outdir = Path(cfg.models_dir / model.get("output", None))
        if not outdir.exists():
            outdir.mkdir(parents=True, exist_ok=True)
        outdir = outdir / self.source_file.name
        return outdir

    def generate(self):
        if self.compilable:
            pass
        # Selfie generates binary file as well, but that is not needed
        returncode, output = execute(self.command)
        self.output.unlink()
        if returncode != 0:
            custom_exit(output, cfg.EXIT_MODEL_GENERATION_ERROR)


# def generate_model(file, model_type) -> None:
#     returncode, output = execute(
#         f"{const.rotor_path} -c {file} "
#         f"-o {model_type.output_dir / file.name} "
#         f"{model_type.args}"
#     )
#     outputpath = Path(model_type.output_dir / file.name)
#     outputpath.unlink()
#
#     if returncode != 0:
#         custom_exit(output, const.EXIT_MODEL_GENERATION_ERROR)


def clean_examples() -> None:
    if cfg.models_dir.is_dir():
        shutil.rmtree(cfg.models_dir)


def generate_all_examples() -> None:
    # check if selfie || gcc is available
    # locate examples directory
    # take each individual file and try to create model from it into all possible options
    # check if models directory exists, if it does remove all files inside and 
    clean_examples()
    # prepare directories
        # const.models_dir.mkdir()
        # const.cstar_64_riscv_btor2_path.mkdir(parents=True)
        # const.cstar_64_riscu_btor2_path.mkdir(parents=True)
        # const.cstar_64_riscu_smt_path.mkdir(parents=True)

    files = [file for file in cfg.examples_dir.iterdir()]
    for file in files:
        if file.suffix != ".c":
            continue
        # STARC
        # -----
        # 1) 64-bit architecture risc-u BTOR2
        m = ModelType(file, "starc-64bit-riscv-btor2", True)
        m.generate()
        # generate_model(file, model_generators[CSTAR_64_BIT_RISCU_BTOR])
        # # 2) 64-bit architecture risc-v BTOR2
        # generate_model(file, model_generators[CSTAR_64_BIT_RISCV_BTOR])
        # # 3) 64-bit architecture risc-u SMT2Lib
        # generate_model(file, model_generators[CSTAR_64_BIT_RISCU_SMT])

        print("Generating example models done!")
