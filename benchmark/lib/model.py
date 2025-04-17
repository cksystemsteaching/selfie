from lib.model_parser import SMT2ModelParser, BTORModelParser
from lib.model_generation_config import ModelBaseConfig, ModelGenerationConfig
from lib.model_presenter import SMT2ModelPresenter, OutputFormat
from lib.model_data import SMT2ModelData, BasicModelData, ParsedSMT2ModelData, SolverRunData, GenerationModelData
import lib.config as cfg

class Model:
    def __init__(self, model_config: ModelBaseConfig, data, presenter):
        # At this point output must be generated already
        if not model_config.get_model_path().exists():
            raise ValueError(f"Can not create model object from {self.output_path}, path does not exists")

        self._data = data
        self._presenter = presenter

    def show(self):
        self._presenter.show(format=OutputFormat.VERBOSE if cfg.verbose else OutputFormat.PLAIN)

    @property
    def data(self) -> SMT2ModelData:
        """Main data access point."""
        return self._data
    
    # Shortcut: model["key"] -> model.data["key"]
    def __getitem__(self, key):
        return self.data[key]

    def add_solver_run(self, solver_run: SolverRunData):
        self._data.solver_runs.append(solver_run)
class SMT2Model(Model):

    def __init__(self, model_config: ModelBaseConfig):
        data = SMT2ModelData(
            basic=BasicModelData.generate(model_config),
            parsed=ParsedSMT2ModelData.generate(parser=SMT2ModelParser(model_config.get_model_path())),
            generation= GenerationModelData.generate(model_config) if isinstance(model_config, ModelGenerationConfig) else None,
            solver_runs=[]
        )
        super().__init__(model_config, data, SMT2ModelPresenter(self))

class BTORModel(Model):
    def __init__(self, model_config: ModelBaseConfig):
        super().__init__(model_config)

    #TODO    

allowed_models = {
    "smt2": SMT2Model,
    "btor2": BTORModel
}

# Assert that cfg.config["allowed_languages"] contains exactly the same keys as allowed_models
assert (set(cfg.config["allowed_formats"]) == set(allowed_models.keys()))

def model_factory(model_config: ModelBaseConfig):
    format_name = model_config.format
    if format_name not in allowed_models:
        raise ValueError(f"Unknown model format: {format_name}. Available: {list(allowed_models.keys())}")
    model_class = allowed_models[model_config.format]
    return model_class(model_config)