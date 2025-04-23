import lib.config as cfg
from lib.solver import available_solvers

import argparse

def init_parser():
    parser = argparse.ArgumentParser(description="Tool for generating SMT models from RISC-V machine code and benchmarking SMT solvers using these models")

    parser.add_argument(
        '-m', '--model-base',
        required=False,
        help="Specify models, you can find available models in config and add new ones",
        default="starc-32bit-riscv-smt"
    )

    parser.add_argument(
        '-s', '--source',
        required=False,
        help="Source file"
    )

    parser.add_argument(
        '-sl', '--solver',
        required=False,
        help=f"Provide a solver, otherwise no solver will be invoked. Available solvers: {list(available_solvers.keys())}"
    )

    parser.add_argument(
        '-o', '--output',
        required=False,
        default=cfg.config["default_output"],
        help="Output path for the generated model - if not provided BT will generate one from source path and model type"
    )
    
    parser.add_argument(
        '-v', '--verbose',
        action='store_true',  # Sets `verbose=True` if flag is present
        default=False,
        help="Enable verbose logging."
    )

    parser.add_argument(
        '-g', '--graph',
        action='store_true',
        help="Provide graphs for the models"
    )

    parser.add_argument(
        '-t', '--timeout',
        default=600,
        type=int,
        help="Set timeout for the solver",
    )

    parser.add_argument(
        '-l', '--load',
        required=False,
        help="Load models"
    )

    return parser
