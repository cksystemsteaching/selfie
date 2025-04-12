import lib.config as cfg
from lib.generate import generate_all_examples, clean_examples, create_models, load_models
from lib.print import custom_exit
import lib.argument_parser as arg_parser
from lib.solver import Z3Solver
from lib.paths import SourcePath, LoadSourcePath, OutputPath
from lib.log import configure_logging
from lib.model_grapher import GrapherWrapper
import logging
import sys

if __name__ == "__main__":
    parser = arg_parser.init_parser()
    args = parser.parse_args()

    if len(sys.argv) <= 1:
        parser.print_help()
        exit()

    # Initialize logging
    configure_logging(args.verbose, OutputPath("bt.log"))
    cfg.verbose = args.verbose
    logger = logging.getLogger('bt')

    if args.clean:
        clean_examples()
        logger.info("Output directories cleaned.")

    if args.generate_examples:
        generate_all_examples()
        logger.info("Generated all examples sucessfuly.")

    models = []

    if args.load:
        loaded_models = load_models(LoadSourcePath(args.load))
        models.extend(loaded_models)
        for model in loaded_models:
            model.show()

    if args.source:
        genereated_models = create_models(SourcePath(args.source), args.model_base, OutputPath(args.output))
        for model in genereated_models:
            model.show()
        
        models.extend(genereated_models)
    
    if args.benchmark:
        for model in models:
            Z3Solver(model, 10).benchmark()

    if args.graph:
        grapher = GrapherWrapper(OutputPath(args.output), models)
        grapher.generate_graphs()