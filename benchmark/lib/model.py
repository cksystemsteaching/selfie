from lib.model_parser import SMT2ModelParser, BTORModelParser
from lib.paths import OutputPath
from lib.model_generation_config import ModelGenerationConfig
from lib.model_presenter import SMT2ModelPresenter, OutputFormat
import lib.config as cfg

class Model:
    def __init__(self, output_path, parser):
        self.output_path = output_path
        # At this point output must be generated already
        if not self.output_path.exists():
            raise ValueError(f"Can not create model object from {self.output_path}, path does not exists")
        self.parser = parser

    def log(self):
        self.parser.parse()
        self.parser.log()


class SMT2Model(Model):
    def __init__(self, output_path: OutputPath):
        super().__init__(output_path, SMT2ModelParser(output_path))

    def show(self):
        presenter = SMT2ModelPresenter(self)
        print(cfg.verbose)
        presenter.show(format=OutputFormat.VERBOSE if cfg.verbose else OutputFormat.PLAIN)  # Simple text

class BTORModel(Model):
    def __init__(self, output_path: OutputPath):
        super().__init__(output_path, BTORModelParser(output_path))
    
    def show(self):
        pass

allowed_models = {
    "smt2": SMT2Model,
    "btor2": BTORModel
}

# Assert that cfg.config["allowed_languages"] contains exactly the same keys as allowed_models
assert (set(cfg.config["allowed_formats"]) == set(allowed_models.keys()))

def model_factory(model_config: ModelGenerationConfig):
    format_name = model_config.model_type.get_format()
    if format_name not in allowed_models:
        raise ValueError(f"Unknow model format: {format_name}. Available: {list(allowed_models.keys())}")
    model_class = allowed_models[model_config.model_type.get_format()]
    return model_class(model_config.output_path)