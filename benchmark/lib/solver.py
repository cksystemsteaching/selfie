from lib.model import Model
from lib.exceptions import UnsupportedModelException, BTValueError
from lib.checks import is_tool_available
from lib.model_data import SolverData

import subprocess
import time
from typing import Dict, Any

import logging

logger = logging.getLogger("bt.solver")


class BaseSolver:
    def __init__(self):
        self.data = SolverData()

    def run(self, model: "Model", timeout: int, args: Dict[str, Any] = None):
        pass

    def check_model(self, model):
        if model.data.basic.format not in self.get_supported_models():
            raise UnsupportedModelException(
                f"Unsupported model format used in {self.__class__.__name__}",
                model,
                solver=self.__class__.__name__,
            )

    def check_solver(self, model):
        pass


class BaseSDKSolver(BaseSolver):
    def __init__(self):
        super().__init__()


class BaseCLISolver(BaseSolver):
    def __init__(self, solver_command: str):
        super().__init__()
        self.solver_command = solver_command
        self.check_solver()

    def run(self, model: "Model", timeout: int, args: Dict[str, Any] = None):
        """
        Runs the solver command with specified arguments and timeout.

        Args:
            model: The model object containing configuration (e.g., output_path).
            timeout: Maximum execution time in seconds.
            args: A list of additional arguments for the solver command. Defaults to None.

        Returns:
            A dictionary containing execution results:
            'elapsed_time': Wall-clock time taken (float).
            'returncode': Exit code of the process (int), or None if killed/not started.
            'stdout': Captured standard output (str).
            'stderr': Captured standard error (str).
            'success': Boolean indicating success (returncode == 0).
            'timed_out': Boolean indicating if the command timed out.
            'error_message': String description of the error, if any.
        """

        cmd = [self.solver_command]
        cmd.extend(args)
        cmd.append(model.data.basic.output_path.__str__())

        basic_data = {
            "solver_used": self.get_solver_name(),
            "solver_cmd": " ".join(cmd),
        }
        self.data.runs += 1

        try:
            self.check_model(model)
        except UnsupportedModelException as e:
            return {
                **basic_data,
                "elapsed_time": 0.0,
                "returncode": None,
                "stdout": "",
                "stderr": str(e),
                "success": False,
                "timed_out": False,
                "error_message": f"Model check failed: {e}",
            }

        start_time = time.perf_counter()  # Use perf_counter for measuring intervals
        elapsed_time = 0.0  # Initialize elapsed time

        try:
            logger.info(f"Running command: {' '.join(cmd)}")
            logger.info(f"Timeout is set to {timeout}s.")
            # Use subprocess.run
            result = subprocess.run(
                cmd,
                capture_output=True,  # Capture stdout and stderr
                text=True,  # Decode stdout/stderr as text (UTF-8 default)
                timeout=timeout,  # Apply timeout
                check=True,  # Raise CalledProcessError on non-zero exit codes
            )
            elapsed_time = time.perf_counter() - start_time

            # Update solver data
            self.data.avg_solve_time = (
                self.data.avg_solve_time * len(self.data.solved) + elapsed_time
            ) / (len(self.data.solved) + 1)
            self.data.solved.append(model)
            if self.data.shortest_run[0] > elapsed_time:
                self.data.shortest_run = (elapsed_time, model)
            if self.data.longest_run[0] < elapsed_time:
                self.data.longest_run = (elapsed_time, model)

            logger.info(
                f"Solving completed successfully in {elapsed_time:.2f}s. Return code: {result.returncode}"
            )
            return {
                **basic_data,
                "elapsed_time": elapsed_time,
                "returncode": result.returncode,
                "stdout": result.stdout,
                "stderr": result.stderr,
                "success": True,
                "timed_out": False,
                "error_message": None,
            }

        except subprocess.CalledProcessError as e:
            elapsed_time = time.perf_counter() - start_time

            # Update solver data
            self.data.error.append(model)

            logger.error(
                f"Command failed with return code {e.returncode} after {elapsed_time:.2f}s."
            )
            logger.error(f"Stderr:\n{e.stderr.strip()}")
            return {
                **basic_data,
                "elapsed_time": elapsed_time,
                "returncode": e.returncode,
                "stdout": e.stdout,
                "stderr": e.stderr,
                "success": False,
                "timed_out": False,
                "error_message": f"Command '{' '.join(e.cmd)}' returned non-zero exit status {e.returncode}.",
            }

        except subprocess.TimeoutExpired as e:
            # Update solver data
            self.data.error.append(model)

            logger.warning(f"Command timed out after {timeout}s.")
            # Output captured before timeout is available in the exception object
            stdout_before_timeout = (
                e.stdout.decode("utf8", errors="replace") if e.stdout else ""
            )
            stderr_before_timeout = (
                e.stderr.decode("utf8", errors="replace") if e.stderr else ""
            )
            if stdout_before_timeout:
                logging.getLogger("bt-cli").info(
                    f"You can find the stdout output before the timeout in log file."
                )
                logging.getLogger("bt-file").info(
                    f"Parial stdout before timeout:\n{stdout_before_timeout}"
                )
            if stderr_before_timeout:
                logging.getLogger("bt-cli").info(
                    f"You can find stderr output before the timeout in log file."
                )
                logging.getLogger("bt-file").info(
                    f"Partial stderr before timeout:\n{stderr_before_timeout}"
                )
            return {
                **basic_data,
                "elapsed_time": timeout,
                "returncode": None,
                "stdout": stdout_before_timeout,
                "stderr": stderr_before_timeout,
                "success": False,
                "timed_out": True,
                "error_message": f"Command '{' '.join(e.cmd)}' timed out after {e.timeout} seconds.",
            }
        except (
            Exception
        ) as e:  # Catch other potential errors (e.g., permission issues, unexpected OS errors)
            elapsed_time = time.perf_counter() - start_time
            logger.exception(
                f"An unexpected error occurred running command {' '.join(cmd)}: {e}"
            )
            return {
                **basic_data,
                "elapsed_time": elapsed_time,
                "returncode": None,
                "stdout": "",
                "stderr": str(e),
                "success": False,
                "timed_out": False,
                "error_message": f"An unexpected error occurred: {e}",
            }

    def check_solver(self):
        if is_tool_available(self.solver_command):
            return True
        logger.warning(
            f"{self.__class__.__name__} command '{self.solver_command}' is not available. Skipping it."
        )
        return False


class Z3Solver(BaseCLISolver):
    def __init__(self):
        super().__init__("z3")

    def run(self, model: Model, timeout, args=[]):
        arguments = []
        arguments.extend(args)
        return super().run(model, timeout, arguments)

    def benchmark(self):
        logger.info(f"Benchmarking {self.model.name} with Z3")

        benchmark_data = self.run()
        logger.info(f"Execution time: {benchmark_data['elapsed_time']}")

    def get_supported_models(self):
        return {"smt2"}

    def get_solver_name(self):
        return "Z3"


class BitwuzlaSolver(BaseCLISolver):
    def __init__(self):
        super().__init__("bitwuzla")

    def run(self, model: Model, timeout, args=[]):
        arguments = [
            f"--lang",
            f"{model.data.basic.format}",
        ]
        arguments.extend(args)
        return super().run(model, timeout, arguments)

    def get_supported_models(self):
        return {"smt2", "btor2"}

    def get_solver_name(self):
        return "Bitwuzla"


class BitwuzlaSDKSolver(BaseSDKSolver):
    def __init__(self):
        super().__init__()
        self._bitwuzla_module = None  # Will hold the imported module when needed

    @property
    def bitwuzla(self):
        """Lazy-load the bitwuzla module when first accessed"""
        if self._bitwuzla_module is None:
            import bitwuzla

            self._bitwuzla_module = bitwuzla
        return self._bitwuzla_module

    def run(self, model: "Model", timeout: int, args: Dict[str, Any] = None):
        """
        Run the Bitwuzla solver using its Python SDK.

        Args:
            model: The model to solve
            timeout: Timeout in seconds
            args: Additional solver options as a dictionary
        """
        from lib.bitwuzla_terminator import TimeTerminator
        from lib.utils import suppress_stdout

        options = {
            self.bitwuzla.Option.VERBOSITY: 0,
            self.bitwuzla.Option.LOGLEVEL: 0,
        }

        logger.info(
            f"Running SDK solver: {self.get_solver_name()} on {model.data.basic.name}"
        )
        logger.info(f"Timeout is set to {timeout}s.")

        if args:
            options.update(args)

        basic_data = {
            "solver_used": self.get_solver_name(),
            "solver_cmd": f"Bitwuzla SDK with options: {options}",
        }
        self.data.runs += 1

        try:
            self.check_model(model)
        except UnsupportedModelException as e:
            return {
                **basic_data,
                "elapsed_time": 0.0,
                "returncode": None,
                "stdout": "",
                "stderr": str(e),
                "success": False,
                "timed_out": False,
                "error_message": f"Model check failed: {e}",
            }

        start_time = time.perf_counter()
        elapsed_time = 0.0

        result = {
            **basic_data,
            "elapsed_time": 0.0,
            "returncode": None,
            "stdout": "",
            "stderr": "",
            "success": False,
            "timed_out": False,
            "error_message": None,
        }
        try:
            # Create Bitwuzla instance with timeout
            bitwuzla_options = self.bitwuzla.Options()

            # Set options
            for opt, val in options.items():
                bitwuzla_options.set(opt, val)

            if args:  # Override with runtime args if provided
                for opt, val in args.items():
                    bitwuzla_options.set(opt, val)

            parser = self.bitwuzla.Parser(
                self.bitwuzla.TermManager(), bitwuzla_options, model.data.basic.format
            )
            terminator = TimeTerminator(timeout)
            parser.configure_terminator(terminator)

            with suppress_stdout():
                parser.parse(model.data.basic.output_path)

            elapsed_time = time.perf_counter() - start_time

            result.update(
                {
                    "elapsed_time": (
                        elapsed_time if not terminator.activated else timeout
                    ),
                    "returncode": 0 if not terminator.activated else 1,
                    "stdout": f"Result: {result}",
                    "success": not terminator.activated,
                    "timed_out": terminator.activated,
                    "error_message": (
                        "Timeout reached" if terminator.activated else None
                    ),
                }
            )

            if not terminator.activated:
                # Update solver data
                self.data.avg_solve_time = (
                    self.data.avg_solve_time * len(self.data.solved) + elapsed_time
                ) / (len(self.data.solved) + 1)
                self.data.solved.append(model)
                if self.data.shortest_run[0] > elapsed_time:
                    self.data.shortest_run = (elapsed_time, model)
                if self.data.longest_run[0] < elapsed_time:
                    self.data.longest_run = (elapsed_time, model)
            else:
                self.data.timedout.append(model)
                logger.warning(f"Bitwuzla SDK timed out after {elapsed_time:.2f}s")

        except self.bitwuzla.BitwuzlaException as e:
            elapsed_time = time.perf_counter() - start_time
            result.update(
                {
                    "elapsed_time": elapsed_time,
                    "stderr": str(e),
                    "success": False,
                    "error_message": f"{e}",
                }
            )
            self.data.error.append(model)
            logger.error(f"Bitwuzla SDK failed after {elapsed_time:.2f}s: {e}")
        except TimeoutError as e:
            pass

        return result

    def get_solver_name(self):
        return "Bitwuzla-SDK"

    def get_supported_models(self):
        return {"smt2", "btor2"}


available_solvers = {
    "z3": Z3Solver(),
    "bitwuzla": BitwuzlaSolver(),
    "bitwuzla-sdk": BitwuzlaSDKSolver(),
}


def present_solvers():
    from lib.presenter import SolverPresenter
    from lib.config import verbose

    for solver in available_solvers.values():
        if solver.data.runs > 0:
            SolverPresenter(solver).show(verbose)


# Parse solvers from the CLI argument
def parse_solvers(solver_args: str):
    if not solver_args:
        return []

    solver_names = solver_args.split(",")
    solvers = []
    for name in solver_names:
        if name not in available_solvers:
            logger.warning(
                f"Provided solver '{name}' is not valid. Valid ones: {list(available_solvers.keys())}."
            )
        else:
            solvers.append(available_solvers[name])

    if not solvers:
        raise BTValueError(
            f"No valid solvers provided: {solver_args}. Aborting bencharming.",
            {solver_args},
        )
    return solvers
