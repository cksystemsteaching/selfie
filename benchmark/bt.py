import lib.config as cfg
from lib.generate import create_models, load_models
import lib.argument_parser as arg_parser
from lib.paths import SourcePath, LoadSourcePath, OutputPath
from lib.log import configure_logging
from lib.model_grapher import GrapherWrapper
from lib.model_type import get_all_model_types

import lib.solver as slv
import lib.overview as ov

import logging
import sys


def main():
    parser = arg_parser.init_parser()
    args = parser.parse_args()

    if not any([args.source, args.load]):
        parser.print_help()
        return

    # Initialize logging
    configure_logging(args.verbose, OutputPath("bt.log"))
    cfg.verbose = args.verbose
    logger = logging.getLogger("bt")

    models = []
    if args.load:
        logger.info(f"Loading models from source {args.load}")
        loaded_models = load_models(LoadSourcePath(args.load))
        models.extend(loaded_models)
        logger.info(f"Loaded {len(loaded_models)} models")

    if args.source:
        logger.info(
            f"Creating models from {args.source} using {args.model_type} model type base, output to '{args.output}'"
        )

        logger.info("Parsing provided model types...")
        model_types = get_all_model_types(args.model_type)
        logger.info(f"Parsed following model types: {list(model_type.name for model_type in model_types)}")

        generated_models = create_models(
            SourcePath(args.source), model_types, OutputPath(args.output)
        )
        models.extend(generated_models)
        logger.info(f"Created {len(generated_models)} models")

    solvers = []
    if args.solver:
        logger.info("Getting provided solvers...")
        solvers = slv.parse_solvers(args.solver)
        if solvers:
            logger.info(
                f"Solving {len(models)} models using solvers: {[solver.get_solver_name() for solver in solvers]}..."
            )
            logger.info(f"Timeout is set to {args.timeout}s")
            for model in models:
                for solver in solvers:
                    if solver.available:
                        run_data = solver.run(model, args.timeout, [])
                        model.add_solver_data(run_data)

    logger.info("Presenting results:")
    for model in models:
        model.show()

    if solvers:
        slv.present_solvers()

    ov.present_overview(models, solvers)

    if args.graph:
        logger.info("Generating graphs...")
        grapher = GrapherWrapper(OutputPath(args.output), models, solvers)
        grapher.generate_graphs()


if __name__ == "__main__":
    sys.exit(main())
