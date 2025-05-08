import unittest
from unittest.mock import patch, MagicMock, call, create_autospec
from lib.solver import (
    BaseCLISolver,
    Z3Solver,
    available_solvers,
    parse_solvers,
)
from lib.model_generation_config import ModelBaseConfig
from lib.model_data import ModelData, BasicModelData, SolverRunData
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

    @patch("subprocess.Popen")
    def test_run_success(self, mock_popen):
        # Create the complete process mock hierarchy
        mock_process = MagicMock()
        mock_process.__enter__.return_value = mock_process  # Critical for context manager
        mock_process.poll.return_value = 0
        mock_process.pid = 1234
        mock_process.communicate.return_value = ("stdout", "stderr")
        mock_process.returncode = 0 
        
        # Configure Popen to return our mock
        mock_popen.return_value = mock_process
        
        # Mock psutil.Process properly
        with patch("psutil.Process") as mock_psutil:
            mock_psutil.return_value.memory_info.return_value.rss = 0
            mock_psutil.return_value.cpu_percent.return_value = 0
            
            solver = Z3Solver()
            run_data = solver.run(self.model, timeout=10)
            
            # Verify process was created correctly
            mock_popen.assert_called_once()
            
            # Verify results
            assert run_data.success is True
            assert run_data.returncode == 0
            assert not run_data.timed_out
            assert run_data.stdout == "stdout"
            assert run_data.stderr == "stderr"
        
    @patch("subprocess.Popen")
    def test_cli_solver_error(self, mock_popen):
        mock_process = MagicMock()
        mock_process.__enter__.return_value = mock_process 
        mock_process.poll.return_value = 0
        mock_process.pid = 1234
        mock_process.communicate.return_value = ("stdout", "stderr")
        mock_process.returncode = 1
        
        mock_popen.return_value = mock_process
        
        with patch("psutil.Process") as mock_psutil:
            mock_psutil.return_value.memory_info.return_value.rss = 0
            mock_psutil.return_value.cpu_percent.return_value = 0
            
            solver = Z3Solver()
            run_data = solver.run(self.model, timeout=10)
            
            mock_popen.assert_called_once()
            
            assert run_data.success is False
            assert run_data.returncode == 1
            assert not run_data.timed_out
            assert run_data.stdout == "stdout"
            assert run_data.stderr == "stderr"

    @patch("psutil.Process")
    @patch("time.sleep")
    @patch("time.perf_counter")
    def test_run_timeout(self, mock_perf, mock_sleep, mock_psutil_process):
        mock_process = MagicMock()
        mock_process.pid = 1234
        mock_process.poll.side_effect = [None, None, None]

        mock_perf.side_effect = [0.0, 0.0, 15.0]  # Elapse 15s

        # Disable resource tracking
        mock_psutil_process.return_value.memory_info.return_value.rss = 0  # Dummy value
        mock_psutil_process.return_value.cpu_percent.return_value = 0      # Dummy value

        solver = Z3Solver()
        run_data = SolverRunData()
        solver._monitor_process(run_data, mock_process, timeout=10, start_time=0.0, model=self.model)

        assert run_data.timed_out
        assert run_data.elapsed_time == 15.0
        mock_process.kill.assert_called_once()

    @patch("psutil.Process")
    @patch("time.sleep")
    @patch("time.perf_counter")
    def test_monitor_resources(self, mock_perf, mock_sleep, mock_psutil_process):
        mock_process = MagicMock()
        mock_process.pid = 1234
        mock_process.poll.side_effect = [None, 0]

        mock_psutil = MagicMock()
        mock_psutil.memory_info.side_effect = [
            MagicMock(rss=1000000),
            MagicMock(rss=2000000),
        ]
        mock_psutil.io_counters.return_value = MagicMock(
            read_bytes=100, write_bytes=200
        )
        mock_psutil.cpu_percent.return_value = 50.0
        mock_psutil_process.return_value = mock_psutil

        mock_perf.return_value = 0.0

        solver = Z3Solver()
        run_data = SolverRunData()
        solver._monitor_process(run_data, mock_process, timeout=10, start_time=0.0, model=self.model)

        assert run_data.max_rss == 2000000
        assert run_data.max_cpu_percent == 50.0

    def test_update_stats_solved(mock_model):
        solver = BaseCLISolver("solver_cmd")
        run_data = SolverRunData()
        run_data.elapsed_time = 10.0
        run_data.success = True

        solver._update_solver_stats(run_data, mock_model)
        assert len(solver.data.solved) == 1
        assert solver.data.avg_solve_time == 10.0

    def test_update_stats_timed_out(self):
        solver = BaseCLISolver("solver_cmd")
        run_data = SolverRunData()
        run_data.timed_out = True

        solver._update_solver_stats(run_data, self.model)
        assert len(solver.data.timedout) == 1

    # Test _build_command
    def test_build_command_no_args(self):
        solver = BaseCLISolver("solver_cmd")
        cmd = solver._build_command(self.model, args=[])
        assert cmd == ["solver_cmd", self.model.data.basic.output_path.__str__()]

    def test_build_command_with_args(self):
        solver = BaseCLISolver("solver_cmd")
        cmd = solver._build_command(self.model, args=["-arg1", "val"])
        assert cmd == ["solver_cmd", "-arg1", "val", self.model.data.basic.output_path.__str__()]


class TestErrorHandling(unittest.TestCase):
    def test_unsupported_model(self):
        solver = Z3Solver()
        model = MockModel()
        model.data.basic.format = "unsupported"
        result = solver.run(model, timeout=10)
        self.assertIn("model check failed", result["error_message"].lower())

    @patch("subprocess.Popen")
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
