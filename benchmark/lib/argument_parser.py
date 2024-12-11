import argparse

def init_parser():
    parser = argparse.ArgumentParser(description="Tool for generating SMT models from RISC-V machine code and benchmarking SMT solvers using these models")

    parser.add_argument(
        '-m', '--model-type',
        required=False,
        help="Specify models, you can find available models in config and add new ones"
    )

    parser.add_argument(
        '--source', '-s',
        required=False,
        help="Source file"
    )

    parser.add_argument(
        '--clean',
        action="store_true",
        help="Recursively cleans output directories"
    )

    parser.add_argument(
        "--generate-examples",
        action="store_true",
        help="Generate example outputs"
    )

    parser.add_argument(
        '--benchmark', '-b',
        required=False,
        help="Benchmark"

    )

    return parser
