import unittest
from unittest.mock import patch, MagicMock, call, create_autospec
from lib.solver import (
    BaseCLISolver,
    Z3Solver,
    available_solvers,
    parse_solvers,
)
from lib.model_generation_config import ModelBaseConfig
from lib.model_data import ModelData, BasicModelData
from pathlib import Path
from lib.presenter import BasePresenter

from lib.model import Model
import subprocess
import logging


class MockModel(Model):
    def __init__(self):
        # 1. Create a fully mocked Path object
        mock_path = create_autospec(Path, spec_set=True)
        mock_path.exists.return_value = True
        mock_path.__str__.return_value = "/fake/path.smt2"

        # 2. Configure mock ModelBaseConfig
        mock_config = create_autospec(ModelBaseConfig, spec_set=True)
        mock_config.get_model_path.return_value = mock_path

        # 3. Configure mock ModelData
        mock_data = create_autospec(ModelData)
        mock_data.basic = create_autospec(BasicModelData, spec_set=True)
        mock_data.basic.format = "smt2"
        mock_data.basic.output_path = mock_path
        mock_data.basic.name = "test_model"

        # 4. Initialize with all mocked dependencies
        super().__init__(
            model_config=mock_config,
            data=mock_data,
            presenter=create_autospec(BasePresenter, spec_set=True),
        )


# Configure logging to capture logs during testing
logging.basicConfig(level=logging.DEBUG)
logger = logging.getLogger("bt.solver")


class TestBaseCLISolver(unittest.TestCase):

    # Test the unit test command
    def test_unavailable_solver(self):
        solver = BaseCLISolver("unavailable_solver")
        self.assertFalse(solver.available)

    @patch("lib.solver.is_tool_available")
    def test_solver_available(self, mock_is_tool):
        mock_is_tool.return_value = True
        solver = BaseCLISolver("valid_solver")
        mock_is_tool.assert_called_once_with("valid_solver")  # Verify correct call
        self.assertTrue(solver.available)

    @patch("lib.solver.is_tool_available")
    def test_check_solver_unavailable(self, mock_is_tool):
        mock_is_tool.return_value = False
        solver = BaseCLISolver("fake_solver")
        mock_is_tool.assert_called_once_with("fake_solver")  # Verify correct call
        self.assertFalse(solver.available)


class TestCLISolvers(unittest.TestCase):
    def setUp(self):
        self.model = MockModel()
        self.timeout = 10

    @patch("subprocess.run")
    @patch.object(logger, "info")
    def test_z3_solver_success(self, mock_log, mock_subprocess):
        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "success"
        mock_result.stderr = ""
        mock_subprocess.return_value = mock_result

        solver = Z3Solver()
        result = solver.run(self.model, self.timeout)
        self.assertTrue(result["success"])
        self.assertEqual(result["solver_used"], "Z3")

    @patch("subprocess.run")
    def test_cli_solver_timeout(self, mock_subprocess):
        mock_subprocess.side_effect = subprocess.TimeoutExpired(cmd="z3", timeout=10)

        solver = Z3Solver()
        result = solver.run(self.model, self.timeout)
        mock_subprocess.called_once()
        self.assertTrue(result["timed_out"])
        self.assertIn("timed out", result["error_message"])

    @patch("subprocess.run")
    def test_cli_solver_error(self, mock_subprocess):
        mock_subprocess.side_effect = subprocess.CalledProcessError(
            returncode=1, cmd="z3", stderr="Error"
        )

        solver = Z3Solver()
        result = solver.run(self.model, self.timeout)
        mock_subprocess.called_once()
        self.assertFalse(result["success"])
        self.assertEqual(result["returncode"], 1)


class TestErrorHandling(unittest.TestCase):
    def test_unsupported_model(self):
        solver = Z3Solver()
        model = MockModel()
        model.data.basic.format = "unsupported"
        result = solver.run(model, timeout=10)
        self.assertIn("model check failed", result["error_message"].lower())

    @patch("subprocess.run")
    def test_general_exception_handling(self, mock_subprocess):
        mock_subprocess.side_effect = Exception("Unexpected error")
        solver = Z3Solver()
        result = solver.run(MockModel(), timeout=10)
        self.assertIn("unexpected error", result["error_message"].lower())


class TestSolverUtilities(unittest.TestCase):
    def test_parse_solvers(self):
        # Get all solver names from available_solvers
        all_solver_names = list(available_solvers.keys())
        test_input = ",".join(all_solver_names)

        # Test parsing
        solvers = parse_solvers(test_input)

        # Verify results
        self.assertEqual(len(solvers), len(all_solver_names))
        for solver, expected_class in zip(solvers, available_solvers.values()):
            self.assertIsInstance(solver, expected_class.__class__)

    def test_parse_invalid_solver(self):
        with self.assertLogs(logger="bt.solver", level="WARNING"):
            solvers = parse_solvers("invalid")
            self.assertEqual(len(solvers), 0)
