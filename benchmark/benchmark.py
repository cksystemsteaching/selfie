from lib.checks import check_needed_tools
from lib.exceptions import ToolNotAvailableError, DirectoryNotFoundError, InternalToolNotAvailableError, TimeoutException
import lib.config as cfg
from lib.generate import generate_all_examples, clean_examples, ModelType
from lib.print import custom_exit
import lib.argument_parser as arg_parser
from lib.smt_benchmark import benchmark_model

if __name__ == "__main__":
    try:
        args = arg_parser.parse_arguments()

        check_needed_tools()

        if args.clean:
            clean_examples()
            custom_exit("Output directories cleaned")

        if args.generate_examples:
            generate_all_examples()
            custom_exit("Generated all examples sucessfuly")

        if args.model_type and args.source_file:
            ModelType(args.source_file, args.model_type).generate()
            benchmark_model(
                "../models/division-by-zero-3-35-kmin-76-kmax-106-rotorized.smt"
            )
            exit(0)

        if not args.model_type:
            custom_exit("ERROR: --model-type is required")

        if not args.source_file:
            custom_exit("ERROR: --source-file is required")

    except ToolNotAvailableError as e:
        custom_exit(str(e), cfg.EXIT_TOOL_NOT_FOUND)
    except DirectoryNotFoundError as e:
        custom_exit(str(e), cfg.EXIT_TOOL_NOT_FOUND)
    except InternalToolNotAvailableError as e:
        custom_exit(str(e), cfg.EXIT_TOOL_NOT_FOUND)
    except TimeoutException as e:
        custom_exit(str(e), cfg.EXIT_MODEL_GENERATION_ERROR)
