from lib.checks import check_needed_tools
from lib.exceptions import ToolNotAvailableError, DirectoryNotFoundError, InternalToolNotAvailableError, TimeoutException
import lib.config as cfg
from lib.generate import generate_all_examples, clean_examples, create_model
from lib.print import custom_exit
import lib.argument_parser as arg_parser
from lib.smt_benchmark import benchmark_model
from lib.solver import Z3Solver

from pathlib import Path
import sys

if __name__ == "__main__":
    try:
        parser = arg_parser.init_parser()
        args = parser.parse_args()

        if len(sys.argv) <= 1:
            parser.print_help()
            exit()

        if args.clean:
            clean_examples()
            custom_exit("Output directories cleaned")

        if args.generate_examples:
            generate_all_examples()
            custom_exit("Generated all examples sucessfuly")

        if args.model_type and args.source:
            model_path = create_model(args.source, args.model_type)
            Z3Solver(Path("../models/model.smt")).benchmark()
            Z3Solver(model_path).benchmark()
            exit(0)

        if not args.model_type and args.source:
            custom_exit("ERROR: --model-type is required")

        if not args.source and args.model_type:
            custom_exit("ERROR: --source-file is required")

        check_needed_tools()

    except ToolNotAvailableError as e:
        custom_exit(str(e), cfg.EXIT_TOOL_NOT_FOUND)
    except DirectoryNotFoundError as e:
        custom_exit(str(e), cfg.EXIT_DIRECTORY_NOT_FOUND)
    except InternalToolNotAvailableError as e:
        custom_exit(str(e), cfg.EXIT_TOOL_NOT_FOUND)
    except TimeoutException as e:
        custom_exit(str(e), cfg.EXIT_MODEL_TIMEOUT_ERROR)
