import lib.config as cfg
from lib.solver import available_solvers

import argparse


def init_parser() -> argparse.ArgumentParser:
    """Initialize and configure the command-line argument parser for the SMT model tool."""

    parser = argparse.ArgumentParser(
        description="Tool for generating SMT models from RISC-V machine code and benchmarking SMT solvers using these models"
    )

    parser.add_argument(
        "-m",
        "--model-type",
        required=False,
        help="""
        Specifies model builder options and compilation commands. Available types are defined in the config file (e.g., 'starc-32bit-riscv-smt2', 'gcc-rv32im-btor2').
        Use 'all' to process all available models.""",
        default=cfg.config["default_model_type"],
    )

    parser.add_argument(
        "-s",
        "--source",
        required=False,
        help=f"""Path to the input source file/directory.
        Supported formats: {list(cfg.config['allowed_languages'])}""",
    )

    parser.add_argument(
        "-l",
        "--load",
        required=False,
        help=f"""Path to the input load file/directory.
        Supported formats: {list(cfg.config['allowed_formats'])}""",
    )

    parser.add_argument(
        "-sl",
        "--solver",
        required=False,
        help=f"Specify which SMT solver to use for benchmarking. Available solvers: {list(available_solvers.keys())}. Note: If not specified, only model generation will be performed.",
    )

    parser.add_argument(
        "-t",
        "--timeout",
        default=600,
        type=int,
        help="""Maximum time (in seconds) allowed for solver execution.
Default: %(default)s seconds (10 minutes)""",
    )

    parser.add_argument(
        "-o",
        "--output",
        required=False,
        default=cfg.config["default_output"],
        help=f"""Output path for the generated model - if not provided BT will generate one from source path and model type. 
        Note: Only provide an output directory when loading/sourcing a directory."
        Default output path from config: {cfg.config['default_output']}
        """,
    )

    parser.add_argument(
        "-v",
        "--verbose",
        action="store_true",
        default=False,
        help="Enable verbose logging.",
    )

    parser.add_argument(
        "-g",
        "--graph",
        action="store_true",
        help="Generate visualization graphs for the analysis. Graphs will be saved in the output directory.",
    )

    return parser
