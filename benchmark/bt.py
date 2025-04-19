import lib.config as cfg
from lib.generate import generate_all_examples, clean_examples, create_models, load_models
from lib.print import custom_exit
import lib.argument_parser as arg_parser
from lib.paths import SourcePath, LoadSourcePath, OutputPath
from lib.log import configure_logging
from lib.model_grapher import GrapherWrapper

import lib.solver as slv
import lib.overview as ov 

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

    if args.source:
        genereated_models = create_models(SourcePath(args.source), args.model_base, OutputPath(args.output))
        models.extend(genereated_models)
    
    if args.solver:
        solvers = slv.parse_solvers(args.solver)

        for model in models:
            for solver in solvers:
                result = solver.run(model, args.timeout, [])
                model.add_solver_data(result)
    
    for model in models:
        model.show()

    if args.solver:
        slv.present_solvers()

    ov.present_overview(models, slv.parse_solvers(args.solver))

    if args.graph:
        grapher = GrapherWrapper(OutputPath(args.output), models)
        grapher.generate_graphs()