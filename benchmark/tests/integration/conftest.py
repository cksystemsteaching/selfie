import pytest
import subprocess
import stat
import tempfile
from pathlib import Path
import os


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
(set-logic QF_AUFBV)

;; Declare a 32-bit bitvector variable
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))

;; Declare an array from 32-bit addresses to 8-bit values
(declare-fun mem () (Array (_ BitVec 32) (_ BitVec 8)))

;; Assert that x + y > 0 (bitvector comparison)
(assert (bvugt (bvadd x y) (_ bv0 32)))

;; Assert that memory at address x is equal to #xFF
(assert (= (select mem x) #xFF))

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


def create_fake_solver(script_content):
    """Creates a temporary executable script and returns its path."""
    fd, path = tempfile.mkstemp(suffix=".py")
    os.write(fd, script_content.encode())
    os.close(fd)
    os.chmod(path, stat.S_IRWXU)  # Make executable (700)
    return path


@pytest.fixture
def fake_z3(tmp_path, request):
    """Creates a fake Z3 binary with optional delay.

    Usage:
    @pytest.mark.parametrize("fake_z3", [{"delay": 2}], indirect=True)
    def test_slow_solver(fake_z3):
        ...
    """
    # Default: no delay unless specified in @parametrize
    delay = request.param.get("delay", 0) if hasattr(request, "param") else 0

    fake_z3_script = f"""#!/usr/bin/env bash
sleep {delay}  # Simulate solver computation time
echo "sat"     # Standard response
"""
    fake_z3_path = tmp_path / "z3"
    fake_z3_path.write_text(fake_z3_script)
    fake_z3_path.chmod(0o755)

    # Override PATH (prefer tmp_path)
    old_path = os.environ["PATH"]
    os.environ["PATH"] = f"{tmp_path}:{old_path}"

    yield str(fake_z3_path)

    # Restore PATH
    os.environ["PATH"] = old_path


@pytest.fixture
def fake_bitwuzla(tmp_path, request):
    """Creates a fake Bitwuzla binary with optional delay.

    Usage:
    @pytest.mark.parametrize("fake_bitwuzla", [{"delay": 2}], indirect=True)
    def test_slow_solver(fake_bitwuzla):
        ...
    """

    # Default: no delay unless specified in @parametrize
    delay = request.param.get("delay", 0) if hasattr(request, "param") else 0

    # Create the fake solver script
    fake_bitwuzla_script = f"""#!/usr/bin/env bash
sleep {delay}  # Simulate solver computation time
echo "sat"     # Standard response
"""
    # Write to a temporary file
    fake_bitwuzla_path = (
        tmp_path / "bitwuzla"
    )  # Filename must match solver binary (e.g., "z3" or "bitwuzla")
    fake_bitwuzla_path.write_text(fake_bitwuzla_script)
    fake_bitwuzla_path.chmod(0o755)  # Make executable

    # Override PATH to prioritize the fake solver
    old_path = os.environ["PATH"]
    os.environ["PATH"] = f"{tmp_path}:{old_path}"

    yield str(fake_bitwuzla_path)  # Provide path to the fake solver

    # Clean up
    os.environ["PATH"] = old_path
