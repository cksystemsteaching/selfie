import pytest
import subprocess
from pathlib import Path


@pytest.fixture
def run_cli():
    """Fixture to execute the CLI tool"""

    def _run(args):
        result = subprocess.run(
            ["python", "-m" "bt"] + args, capture_output=True, text=True
        )
        print(f"Output:\n{result.stdout}")  # Visible with pytest -s
        if result.stderr:
            print(f"Logging:\n{result.stderr}")
        return result

    return _run


@pytest.fixture
def valid_smt2_file(tmp_path):
    """Creates a valid SMT-LIBv2 benchmark file"""
    file = tmp_path / "test.smt2"
    file.write_text(
        """
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (> (+ x y) 0))
(check-sat)
(exit)
"""
    )
    return file


@pytest.fixture
def invalid_smt2_file(tmp_path):
    """Creates a valid SMT-LIBv2 benchmark file"""
    file = tmp_path / "test.smt2"
    file.write_text(
        """
invalid_smtlib_file
(exit)
"""
    )
    return file


@pytest.fixture
def valid_cstar_file(tmp_path):
    """Creates a valid C* file that can work as an input to BT"""
    file = tmp_path / "tmp_input.c"
    file.write_text(
        """
uint64_t main() {
  uint64_t  a;
  uint64_t* x;

  a = 40;
  x = malloc(sizeof(uint64_t));

  *x = 0;

  read(0, x, 1);

  *x = *x - 47;

  if (*x == 2)
    a = a + *x;

  if (a == 42)
    return 1;
  else
    return 0;
}
"""
    )
    return file


@pytest.fixture
def output_dir(tmp_path):
    """Creates and returns a clean output directory"""
    output = tmp_path / "test_output"
    output.mkdir()
    return output
