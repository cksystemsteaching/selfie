from tests.integration.helpers import get_output_path


def test_generation_workflow(valid_cstar_file, output_dir, run_cli):
    """Test the model generation path"""
    model_type = "starc-32bit-riscu-smt2"
    result = run_cli(
        [
            "--source",
            str(valid_cstar_file),
            "--output",
            str(output_dir),
            "--model-base",
            model_type,
        ]
    )

    # Check CLI output
    assert f"Creating models from {str(valid_cstar_file)}" in result.stderr
    assert "Created 1 models" in result.stderr
    assert result.returncode == 0

    # Check that a model was created
    model_file = get_output_path(valid_cstar_file, model_type, output_dir)
    assert model_file.exists()


def test_output_name(valid_cstar_file, output_dir, run_cli):
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


def test_print_help(run_cli):
    """Test if help is printed"""
    result = run_cli([])

    assert result.returncode == 0
    assert "usage:" in result.stdout


def test_print_help_insufficient_args(run_cli):
    """Test no source provided - help should be printed"""
    result = run_cli(["--output", "output.smt2", "--model-base", "model-base-test"])

    assert result.returncode == 0
    assert "usage:" in result.stdout


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
