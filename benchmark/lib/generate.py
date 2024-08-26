import lib.constants as const
from .checks import execute
from .print import custom_exit

from pathlib import Path
import shutil


def generate_model(file, args, output_dir) -> None:
    returncode, output = execute(f"{const.rotor_path} -c {file} -o {output_dir / file.name} {args}")
    outputpath = Path(output_dir / file.name)
    outputpath.unlink()

    if returncode != 0:
        custom_exit(output, const.EXIT_MODEL_GENERATION_ERROR)


def generate_starc_64_bit_riscu(file) -> None:
    generate_model(file, "- 1 -riscuonly", const.starc_64_riscu_path)


def generate_starc_64_bit_riscv(file) -> None:
    generate_model(file, "- 1", const.starc_64_riscv_path)


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
    const.starc_64_riscv_path.mkdir(parents=True)
    const.starc_64_riscu_path.mkdir(parents=True)
    const.starc_64_riscu_path.mkdir(parents=True)

    files = [file for file in const.examples_dir.iterdir()]
    for file in files:
        if file.suffix != ".c":
            continue
        # STARC
        # -----
        # 1) 64-bit architecture risc-u
        generate_starc_64_bit_riscu(file)
        # 2) 64-bit architecture risc-v
        generate_starc_64_bit_riscv(file)
