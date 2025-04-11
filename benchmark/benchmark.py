import lib.config as cfg
from lib.generate import generate_all_examples, clean_examples, create_models
from lib.print import custom_exit
import lib.argument_parser as arg_parser
from lib.solver import Z3Solver
from lib.paths import SourcePath, OutputPath
from lib.log import configure_logging

import sys
import logging

if __name__ == "__main__":
    parser = arg_parser.init_parser()
    args = parser.parse_args()

    if len(sys.argv) <= 1:
        parser.print_help()
        exit()

    # Initialize logging
    verbosity = args.verbosity or 4
    configure_logging(verbosity, OutputPath("bt.log"))

    if args.clean:
        clean_examples()
        custom_exit("Output directories cleaned")

    if args.generate_examples:
        generate_all_examples()
        custom_exit("Generated all examples sucessfuly")

    if args.source:
        models = create_models(SourcePath(args.source), args.model_base, OutputPath(args.output))
        for model in models:
            model.show()
            
        if args.benchmark:
            for model in models:
                Z3Solver(model, 10).benchmark()
            exit(0)

    if not args.source:
        custom_exit("ERROR: --source-file is required")
