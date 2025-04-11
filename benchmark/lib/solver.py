from lib.model import Model

from pathlib import Path
import subprocess
import time

import logging
logger = logging.getLogger("bt.solver")

class BaseSolver:
    def __init__(self, model_path: Model, timeout: int):
        self.model_path = model_path
        self.timeout = timeout

    def run():
        raise NotImplementedError("Abstract method")


class Z3Solver(BaseSolver):
    def __init__(self, model_path: Path):
        super().__init__(model_path)

    def run(self):
        self.check_model()

        start_time = time.time()

        process = subprocess.Popen(
            ['z3', self.model_path],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE
        )

        stdout, stderr = process.communicate()
        end_time = time.time()
        elapsed_time = end_time - start_time

        return {
            'elapsed_time': elapsed_time,
        }


    def benchmark(self):
        # What do I want to print
        # 1. file name, file size, model type
        # 2. solver name, solver settings
        # 3. solver process memory usage
        # 4. solver result
        logger.info(f"Benchmarking {self.model_path.name} with Z3")

        benchmark_data = self.run()
        logger.info(f"Execution time: {benchmark_data['elapsed_time']}")

    # Checks if provided model is digestable by the solver
    def check_model(self):
        if self.model_path.suffix not in self.get_supported_models():
            raise Exception("Unsupported model type for Z3")


    def get_supported_models(self):
        return {
            '.smt'
        }
