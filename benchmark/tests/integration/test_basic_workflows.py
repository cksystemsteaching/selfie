from tests.integration.helpers import get_output_path

def test_generation_workflow(valid_cstar_file, output_dir, run_cli):
    """Test the model generation path"""
    model_type = "starc-32bit-riscu-smt2"
    result = run_cli([
        "--source", str(valid_cstar_file),
        "--output", str(output_dir),
        "--model-base", model_type
    ])

    # Check CLI output
    assert f"Creating models from {str(valid_cstar_file)}" in result.stderr
    assert "Created 1 models" in result.stderr
    assert result.returncode == 0

    #Check that a model was created
    input_name = valid_cstar_file.stem
    model_file = get_output_path(valid_cstar_file, model_type, output_dir)
    assert(model_file.exists())


def test_wrong_input_file_format(tmp_path, run_cli):
    empty_file = tmp_path / "empty.cpp"
    empty_file.touch()
    result = run_cli(["--source", str(empty_file)])
    assert(f"Source extension '{tmp_path.suffix}' not allowed.")
    