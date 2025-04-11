import lib.config as cfg

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
        '--clean',
        action="store_true",
        required=False,
        help="Recursively cleans directories that were used to store examples"
    )

    parser.add_argument(
        "--generate-examples",
        action="store_true",
        help="Generate example outputs"
    )

    parser.add_argument(
        '-b', '--benchmark',
        required=False,
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

    return parser
