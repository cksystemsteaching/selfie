"""
Solver classes. Currently supported solver running from CLI (Bitwuzla, Z3) and as Python libraries (PyBitwuzla).
"""

from lib.model import Model
from lib.exceptions import UnsupportedModelException, BTValueError
from lib.utils import is_tool_available
from lib.model_data import SolverData, SolverRunData

import psutil
import subprocess
import time
from typing import Dict, Any

import logging

logger = logging.getLogger("bt.solver")


class BaseSolver:
    def __init__(self):
        self.data = SolverData()
        self.available = False

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


class BasePySolver(BaseSolver):
    def __init__(self):
        super().__init__()


class BaseCLISolver(BaseSolver):
    def __init__(self, solver_command: str):
        super().__init__()
        self.solver_command = solver_command
        self.available = self.check_solver()

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
        cmd = self._build_command(model, args)
        logger.info(f"Solving {model.data.basic.name} with {self.get_solver_name()}...")

        run_data = SolverRunData()
        run_data.solver_used = self.get_solver_name()
        run_data.solver_cmd = " ".join(cmd)

        try:
            self.check_model(model)
            start_time = time.perf_counter()

            with subprocess.Popen(
                cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True
            ) as process:
                self._monitor_process(run_data, process, timeout, start_time, model)

        except UnsupportedModelException as e:
            run_data.error_message = f"Model check failed: {e}"
            return run_data

        except Exception as e:
            logger.exception(
                f"An unexpected error occurred running command {' '.join(cmd)}: {e}"
            )
            run_data.error_message = f"An unexpected error occurred: {e}"
            return run_data

        self._handle_completion(run_data, process, model)
        return run_data

    def _build_command(self, model: Model, args):
        cmd = [self.solver_command]
        cmd.extend(args)
        cmd.append(model.data.basic.output_path.__str__())
        return cmd

    def _monitor_process(self, run_data: SolverRunData, process, timeout, start_time, model):
        ps_process = None
        next_log_time = -1

        try:
            ps_process = psutil.Process(process.pid)
        except psutil.NoSuchProcess:
            return

        while True:
            try:
                rss = ps_process.memory_info().rss
                cpu_percent = ps_process.cpu_percent(interval=0.1)

                run_data.max_rss = max(run_data.max_rss, rss)
                run_data.max_cpu_percent = max(run_data.max_cpu_percent, cpu_percent)

                if run_data.elapsed_time > next_log_time:
                    rss_in_mb = rss / (1024**2)
                    logger.info(f"Solving for {run_data.elapsed_time:.1f}s | "
                                f"RAM: {rss_in_mb:.1f}MB | "
                                f"CPU: {cpu_percent}%")
                    self.data.profile.record_sample(model, run_data.elapsed_time, rss_in_mb, cpu_percent)
                    next_log_time = run_data.elapsed_time + 10

            except (psutil.NoSuchProcess, psutil.AccessDenied):
                break

            run_data.elapsed_time = time.perf_counter() - start_time
            if run_data.elapsed_time > timeout:
                process.kill()
                run_data.timed_out = True
                break

            if process.poll() is not None:
                break

            time.sleep(0.05)


    def _handle_completion(self, run_data: SolverRunData, process, model: Model):
        run_data.stdout, run_data.stderr = process.communicate()
        run_data.returncode = process.returncode
        run_data.max_rss = run_data.max_rss / (1024**2)  # Convert to MB

        if run_data.timed_out:
            logger.warning(f"Timeout after {run_data.elapsed_time:.2f}s")

        elif run_data.returncode != 0:
            logger.warning(f"Failed with code {run_data.returncode}")
        else:
            run_data.success = True
            logger.info(
                f"Solved in {run_data.elapsed_time:.2f}s | "
                f"Max RAM: {run_data.max_rss:.1f}MB | "
                f"CPU Peak: {run_data.max_cpu_percent}%"
            )

        self._update_solver_stats(run_data, model)
    
    def get_solver_name():
        pass

    def _update_solver_stats(self, run_data: SolverRunData, model: Model):
        self.data.runs += 1
        if run_data.timed_out:
            self.data.timedout.append(model)

        elif run_data.returncode != 0:
            self.data.error.append(model)

        else:
            self.data.avg_solve_time = (
                self.data.avg_solve_time * len(self.data.solved) + run_data.elapsed_time
            ) / (len(self.data.solved) + 1)
            self.data.solved.append(model)

            if run_data.elapsed_time < self.data.shortest_run[0]:
                self.data.shortest_run = (run_data.elapsed_time, model)

            if run_data.elapsed_time > self.data.longest_run[0]:
                self.data.longest_run = (run_data.elapsed_time, model)

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

    def get_supported_models(self):
        return {"smt2"}

    def get_solver_name(self):
        return "z3"


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
        return "bitwuzla"


class PyBitwuzlaSolver(BasePySolver):
    def __init__(self):
        super().__init__()
        self.available = self.check_solver()

    def check_solver(self):
        try:
            import bitwuzla
        except ImportError:
            return False
        return True

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
        import bitwuzla

        options = {
            bitwuzla.Option.VERBOSITY: 0,
            bitwuzla.Option.LOGLEVEL: 0,
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
            bitwuzla_options = bitwuzla.Options()

            # Set options
            for opt, val in options.items():
                bitwuzla_options.set(opt, val)

            if args:  # Override with runtime args if provided
                for opt, val in args.items():
                    bitwuzla_options.set(opt, val)

            parser = bitwuzla.Parser(
                bitwuzla.TermManager(), bitwuzla_options, model.data.basic.format
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

        except bitwuzla.BitwuzlaException as e:
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
            logger.error(f"PyBitwuzla failed after {elapsed_time:.2f}s: {e}")
        except TimeoutError as e:
            pass

        return result

    def get_solver_name(self):
        return "bitwuzla-py"

    def get_supported_models(self):
        return {"smt2", "btor2"}


available_solvers = {
    "z3": Z3Solver(),
    "bitwuzla": BitwuzlaSolver(),
    "bitwuzla-py": PyBitwuzlaSolver(),
}


def present_solvers():
    from lib.presenter import SolverPresenter
    from lib.config import verbose

    for solver in available_solvers.values():
        if solver.data.runs > 0:
            SolverPresenter(solver).show(verbose)


# Parse solvers from the CLI argument
def parse_solvers(solver_args: str):
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
        logger.warning(f"No valid solvers provided: {solver_args}.")

    return solvers
