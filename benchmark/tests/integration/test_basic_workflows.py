from tests.integration.helpers import get_output_path
import pytest


def test_generation_workflow(valid_cstar_file, output_dir, run_cli):
    """Test the model generation path"""
    result = run_cli(
        [
            "--source",
            str(valid_cstar_file),
            "--output",
            str(output_dir),
        ]
    )

    # Check CLI output
    assert f"Creating models from {str(valid_cstar_file)}" in result.stderr
    assert "Created 1 models" in result.stderr
    assert result.returncode == 0


def test_output_name_provided(valid_cstar_file, output_dir, run_cli):
    """Test the model generation path provided a specific output path (not a directory)"""
    output_path = output_dir / "test.smt2"
    result = run_cli(
        [
            "--source",
            str(valid_cstar_file),
            "--output",
            str(output_path),
        ]
    )
    # Check CLI output
    assert f"Creating models from {str(valid_cstar_file)}" in result.stderr
    assert "Created 1 models" in result.stderr
    assert result.returncode == 0
    # Check that a model was created
    assert output_path.exists()


def test_output_name_not_provided(valid_cstar_file, output_dir, run_cli):
    model_type = "starc-32bit-riscu-smt2"
    result = run_cli(["--source", str(valid_cstar_file), "--output", str(output_dir), "--model-type", model_type])

    # Check that a model was created
    model_file = get_output_path(valid_cstar_file, model_type, output_dir)
    assert model_file.exists()
    assert result.returncode == 0


def test_invalid_output_directory(valid_cstar_file, run_cli):
    result = run_cli(
        ["--source", str(valid_cstar_file), "--output", "./non_existent_directory"]
    )
    assert "Parent directory of provided output does not exist" in result.stderr
    assert result.returncode == 1


def test_print_help(run_cli):
    """Test if help is printed"""
    result = run_cli([])

    assert result.returncode == 0
    assert "usage:" in result.stdout


def test_print_help_insufficient_args(run_cli):
    """Test no source provided - help should be printed"""
    result = run_cli(["--output", "output.smt2", "--model-type", "model-type-test"])

    assert result.returncode == 0
    assert "usage:" in result.stdout


def test_all_model_type_keyword(run_cli, valid_cstar_file, output_dir):
    """Test 'all' argument for model types"""
    result = run_cli(
        [
            "--source",
            str(valid_cstar_file),
            "--output",
            str(output_dir),
            "--model-type",
            "all",
        ]
    )

    assert result.returncode == 0


def test_verbose_model_info(run_cli, valid_smt2_file):
    result = run_cli(["--load", str(valid_smt2_file), "-v"])

    assert "MODEL ANALYSIS" in result.stdout
    assert "BT Overview" in result.stdout
    assert result.returncode == 0


def test_invalid_arg(valid_cstar_file, output_dir, run_cli):
    result = run_cli(
        [
            "--source",
            str(valid_cstar_file),
            "--output",
            str(output_dir),
            "--invalid-arg",
        ]
    )
    assert result.returncode == 2
    assert "usage:" in result.stderr
    assert "unrecognized arguments" in result.stderr


def test_broken_smt_input(run_cli, invalid_smt2_file):
    """Provide a valid file with broken input"""
    result = run_cli(
        [
            "--load",
            str(invalid_smt2_file),
        ]
    )
    assert "a parsing error has occured" in result.stderr
    assert "Skipping invalid model" in result.stderr
    assert result.returncode == 0
    assert "Number of models: 0" in result.stdout


def test_wrong_input_file_format(tmp_path, run_cli):
    empty_file = tmp_path / "empty.cpp"
    empty_file.touch()
    result = run_cli(["--source", str(empty_file)])
    assert result.returncode == 1
    assert f"Source extension '{tmp_path.suffix}' not allowed."


def test_z3(fake_z3, run_cli, valid_smt2_file, tmp_path):
    result = run_cli(["--load", str(valid_smt2_file), "--solver", "z3"])

    expected_lines = [
        "z3 Solver Data",
        "Total runs: 1",
        "Solved runs: 1",
        "Timed out runs: 0",
        "Error runs: 0",
    ]
    assert all(line in result.stdout for line in expected_lines)


def test_bitwuzla(fake_bitwuzla, run_cli, valid_smt2_file):
    fake_path = fake_bitwuzla
    result = run_cli(["--load", str(valid_smt2_file), "--solver", "bitwuzla"])

    expected_lines = [
        "bitwuzla Solver Data",
        "Total runs: 1",
        "Solved runs: 1",
        "Timed out runs: 0",
        "Error runs: 0",
    ]
    assert all(line in result.stdout for line in expected_lines)


def test_invalid_solver(run_cli, valid_smt2_file):
    result = run_cli(["--load", str(valid_smt2_file), "--solver", "invalid_solver"])

    assert "Provided solver 'invalid_solver' is not valid." in result.stderr
    assert "No valid solvers provided" in result.stderr
    assert (
        result.returncode == 0
    )  # BT should still finish sucessfully (without using solvers)


def test_invalid_solver_with_valid_solver(fake_z3, valid_smt2_file, run_cli):
    result = run_cli(["--load", str(valid_smt2_file), "--solver", "invalid_solver,z3"])

    assert "Provided solver 'invalid_solver' is not valid." in result.stderr
    assert "No valid solvers provided" not in result.stderr
    assert (
        result.returncode == 0
    )  # BT should still finish sucessfully (using Z3 solver)


@pytest.mark.parametrize("fake_z3", [{"delay": 2}], indirect=True)
def test_z3_timeout(fake_z3, run_cli, output_dir, valid_smt2_file):
    result = run_cli(
        [
            "--load",
            str(valid_smt2_file),
            "--output",
            str(output_dir),
            "--solver",
            "z3",
            "--timeout",
            "1",
        ]
    )

    assert "Timeout is set to 1s" in result.stderr
    assert "Timeout after" in result.stderr
    assert "z3 Solver Data" in result.stdout
    assert "Timed out runs: 1" in result.stdout
    assert result.returncode == 0


@pytest.mark.parametrize("fake_bitwuzla", [{"delay": 2}], indirect=True)
def test_bitwuzla_timeout(fake_bitwuzla, valid_smt2_file, output_dir, run_cli):
    result = run_cli(
        [
            "--load",
            str(valid_smt2_file),
            "--output",
            str(output_dir),
            "--solver",
            "bitwuzla",
            "--timeout",
            "1",
        ]
    )

    assert "Timeout is set to 1s" in result.stderr
    assert "Timeout after" in result.stderr
    assert "bitwuzla Solver Data" in result.stdout
    assert "Timed out runs: 1" in result.stdout


def test_multiple_solvers(fake_bitwuzla, fake_z3, valid_smt2_file, output_dir, run_cli):
    result = run_cli(
        [
            "--load",
            str(valid_smt2_file),
            "--output",
            str(output_dir),
            "--solver",
            "bitwuzla,z3",
        ]
    )

    assert "Used solvers: bitwuzla,z3" in result.stdout
    assert result.returncode == 0
