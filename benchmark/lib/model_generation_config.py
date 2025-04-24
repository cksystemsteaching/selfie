from lib.model_type import ModelType
from lib.paths import SourcePath, OutputPath


class ModelBaseConfig:
    def __init__(self, source_path: SourcePath, format: str):
        self.source_path = source_path
        self.format = format

    def get_model_path(self):
        pass


class ModelGenerationConfig(ModelBaseConfig):
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
            f"{source_path.path.stem}_{'_'.join(model_type.model_type_bases[:-1])}"
        )
        return filename


class ModelLoadConfig(ModelBaseConfig):
    def __init__(self, source_path: SourcePath):
        super().__init__(source_path, source_path._path.suffix[1:])

    def get_model_path(self):
        return self.source_path
