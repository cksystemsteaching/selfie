import lib.constants as const
from .checks import execute
from .print import custom_exit

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
    def __init__(self, args: str, output_dir: str):
        self.args = args
        self.output_dir = output_dir


model_generators = {
    CSTAR_64_BIT_RISCU_BTOR:    ModelType("- 1 -riscuonly", const.cstar_64_riscu_btor2_path),
    CSTAR_64_BIT_RISCU_SMT:     ModelType("- 1 -riscuonly -k -smt -nocomments", const.cstar_64_riscu_smt_path),
    CSTAR_64_BIT_RISCV_BTOR:    ModelType("- 1", const.cstar_64_riscv_btor2_path),
}


def generate_model(file, model_type) -> None:
    returncode, output = execute(
        f"{const.rotor_path} -c {file} "
        f"-o {model_type.output_dir / file.name} "
        f"{model_type.args}"
    )
    outputpath = Path(model_type.output_dir / file.name)
    outputpath.unlink()

    if returncode != 0:
        custom_exit(output, const.EXIT_MODEL_GENERATION_ERROR)


def clean_examples() -> None:
    if const.models_dir.is_dir():
        shutil.rmtree(const.models_dir)


def generate_all_examples() -> None:
    # check if selfie || gcc is available
    # locate examples directory
    # take each individual file and try to create model from it into all possible options
    # check if models directory exists, if it does remove all files inside and 
    clean_examples()
    # prepare directories
    const.models_dir.mkdir()
    const.cstar_64_riscv_btor2_path.mkdir(parents=True)
    const.cstar_64_riscu_btor2_path.mkdir(parents=True)
    const.cstar_64_riscu_smt_path.mkdir(parents=True)

    files = [file for file in const.examples_dir.iterdir()]
    for file in files:
        if file.suffix != ".c":
            continue
        # STARC
        # -----
        # 1) 64-bit architecture risc-u BTOR2
        generate_model(file, model_generators[CSTAR_64_BIT_RISCU_BTOR])
        # 2) 64-bit architecture risc-v BTOR2
        generate_model(file, model_generators[CSTAR_64_BIT_RISCV_BTOR])
        # 3) 64-bit architecture risc-u SMT2Lib
        generate_model(file, model_generators[CSTAR_64_BIT_RISCU_SMT])

        print("Generating example models done!")
