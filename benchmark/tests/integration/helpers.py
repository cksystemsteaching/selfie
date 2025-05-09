from pathlib import Path

def get_output_path(
        input_path: Path,
        model_type: str,
        output_path: Path,

):
    """Gets the path of the output"""
    from lib.model_generation_config import ModelGenerationConfig
    from lib.model_type import ModelType
    from lib.paths import OutputPath, SourcePath

    config = ModelGenerationConfig(SourcePath(input_path), ModelType(model_type), OutputPath(output_path))
    return config.get_model_path()