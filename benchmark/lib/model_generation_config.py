"""
Model configuration containers that handle:
- Path resolution for generated/loaded models
- Format-specific command generation
- Output naming conventions

Key Classes:
1. ModelBaseConfig: Core path/format handling
2. ModelGenerationConfig: Build process setup
3. ModelLoadConfig: Existing model loader
"""

from lib.model_type import ModelType
from lib.paths import SourcePath, OutputPath


class ModelBaseConfig:
    def __init__(self, source_path: SourcePath, format: str):
        self.source_path = source_path
        self.format = format

    def get_model_path(self):
        pass


class ModelGenerationConfig(ModelBaseConfig):
    """Complete model generation specification.
    
    Args:
        source_path: Source file to process
        model_type: ModelType defining build commands
        output_path: Base output directory
        
    Automatically:
    - Determines output filename (stem + model_type segments)
    - Resolves full output path with proper extension
    """
    def __init__(
        self, source_path: SourcePath, model_type: ModelType, output_path: OutputPath
    ):
        self.model_type = model_type
        super().__init__(source_path, self._determine_format())
        self.compilation_cmd = model_type.get_compile_cmd()
        self.model_generation_cmd = model_type.get_model_generation_cmd()
        self.output_path = output_path.as_file_for(
            self._generate_output_name(source_path, model_type), model_type.get_format()
        )

    def get_model_path(self):
        return self.output_path

    def _determine_format(self):
        return self.model_type.get_format()

    @staticmethod
    def _generate_output_name(source_path: SourcePath, model_type: ModelType):
        filename = (
            f"{source_path.path.stem}_{'_'.join(model_type.get_bases()[:-1])}"
        )
        return filename


class ModelLoadConfig(ModelBaseConfig):
    """Simplified config for loading existing models.
    
    Derives format directly from file extension.
    """
    def __init__(self, source_path: SourcePath):
        super().__init__(source_path, source_path._path.suffix[1:])

    def get_model_path(self):
        return self.source_path
