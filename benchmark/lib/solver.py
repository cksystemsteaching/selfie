from lib.model import Model
from lib.exceptions import UnsupportedModelException
from lib.checks import is_tool_available

from pathlib import Path
import subprocess
import time

import logging
logger = logging.getLogger("bt.solver")

class BaseSolver:
    def __init__(self, solver_command: str):
        self.solver_command = solver_command
        self.check_solver()

    def run(self, model: 'Model', timeout: int = 200, args: list = []):
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
        try:
            self.check_model(model)
        except ValueError as e:
            logger.error(f"Model check failed: {e}")
            return {
                'elapsed_time': 0.0, 'returncode': None, 'stdout': "", 'stderr': str(e),
                'success': False, 'timed_out': False, 'error_message': f"Model check failed: {e}"
            }

        cmd = [self.solver_command]
        cmd.extend(args)
        cmd.append(model.output_path.__str__())

        start_time = time.perf_counter() # Use perf_counter for measuring intervals
        elapsed_time = 0.0 # Initialize elapsed time

        try:
            logger.info(f"Running command: {' '.join(cmd)}")
            # Use subprocess.run
            result = subprocess.run(
                cmd,
                capture_output=True,  # Capture stdout and stderr
                text=True,            # Decode stdout/stderr as text (UTF-8 default)
                timeout=timeout,      # Apply timeout
                check=True,           # Raise CalledProcessError on non-zero exit codes
            )
            elapsed_time = time.perf_counter() - start_time
            logger.info(f"Solving completed successfully in {elapsed_time:.2f}s. Return code: {result.returncode}")
            return {
                'elapsed_time': elapsed_time,
                'returncode': result.returncode,
                'stdout': result.stdout,
                'stderr': result.stderr,
                'success': True,
                'timed_out': False,
                'error_message': None,
            }

        except subprocess.CalledProcessError as e:
            elapsed_time = time.perf_counter() - start_time
            logger.error(f"Command failed with return code {e.returncode} after {elapsed_time:.2f}s.")
            logger.error(f"Stderr:\n{e.stderr.strip()}")
            return {
                'elapsed_time': elapsed_time,
                'returncode': e.returncode,
                'stdout': e.stdout,
                'stderr': e.stderr,
                'success': False,
                'timed_out': False,
                'error_message': f"Command '{' '.join(e.cmd)}' returned non-zero exit status {e.returncode}.",
            }

        except subprocess.TimeoutExpired as e:
            logger.warning(f"Command timed out after {timeout}s.")
            # Output captured before timeout is available in the exception object
            stdout_before_timeout = e.stdout.decode("utf8", errors='replace') if e.stdout else ""
            stderr_before_timeout = e.stderr.decode("utf8", errors='replace') if e.stderr else ""
            if stdout_before_timeout: 
                logging.getLogger("bt-cli").info(f"You can find the stdout output before the timeout in log file.")
                logging.getLogger("bt-file").info(f"Parial stdout before timeout:\n{stdout_before_timeout}")
            if stderr_before_timeout: 
                logging.getLogger("bt-cli").info(f"You can find stderr output before the timeout in log file.")
                logging.getLogger("bt-file").info(f"Partial stderr before timeout:\n{stderr_before_timeout}")

            return {
                'elapsed_time': timeout,
                'returncode': None,
                'stdout': stdout_before_timeout,
                'stderr': stderr_before_timeout,
                'success': False,
                'timed_out': True,
                'error_message': f"Command '{' '.join(e.cmd)}' timed out after {e.timeout} seconds.",
            }

        except FileNotFoundError as e:
            elapsed_time = time.perf_counter() - start_time
            logger.error(f"Solver command not found: {cmd}. Error: {e}")
            return {
                'elapsed_time': elapsed_time,
                'returncode': None,
                'stdout': "",
                'stderr': str(e),
                'success': False,
                'timed_out': False,
                'error_message': f"Solver command not found: {e}",
            }
        except Exception as e: # Catch other potential errors (e.g., permission issues, unexpected OS errors)
            elapsed_time = time.perf_counter() - start_time
            logger.exception(f"An unexpected error occurred running command {' '.join(cmd)}: {e}") # Use logger.exception to include traceback
            return {
                'elapsed_time': elapsed_time,
                'returncode': None,
                'stdout': "",
                'stderr': str(e),
                'success': False,
                'timed_out': False,
                'error_message': f"An unexpected error occurred: {e}",
            }

    def check_solver(self):
        if is_tool_available(self.solver_command):
            return 
        logger.warning(f"{self.__class__.__name__} command '{self.solver_command}' is not available. Skipping it.")

    # Checks if provided model is digestable by the solver
    def check_model(self, model):
        if model.get_format() not in self.get_supported_models():
            raise UnsupportedModelException(f"Unsupported model format used in {self.__class__.__name__} ", self.model, solver=self.__class__.__name__)
    
class Z3Solver(BaseSolver):
    def __init__(self):
        super().__init__("z3")

    def run(self, model: Model, timeout: int=300, args=[]):
        arguments = [
        ]
        arguments.extend(args)
        super().run(model, timeout, arguments)

    def benchmark(self):
        logger.info(f"Benchmarking {self.model.name} with Z3")

        benchmark_data = self.run()
        logger.info(f"Execution time: {benchmark_data['elapsed_time']}")

    def get_supported_models(self):
        return {
            'smt2'
        }
    
class BitwuzlaSolver(BaseSolver):
    def __init__(self):
        super().__init__("bitwuzla")
    
    def run(self,  model: Model, timeout: int, args=[]):
        arguments = [
            f"--lang", f"{model.get_format()}",
        ]
        arguments.extend(args)
        super().run(model, timeout, arguments)
    
    def get_supported_models(self):
        return {
            'smt2',
            'btor2'
        }
    
available_solvers = {
    'z3' : Z3Solver,
    'bitwuzla': BitwuzlaSolver
}