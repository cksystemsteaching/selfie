"""
Model class hierarchy and factory for handling SMT2/BTOR2 models.

Key Components:
1. Model: Base class with common functionality
2. SMT2Model/BTORModel: Format-specific implementations
3. model_factory: Creation interface that validates formats
"""

from lib.model_parser import SMT2ModelParser
from lib.model_generation_config import ModelBaseConfig, ModelGenerationConfig
from lib.presenter import SMT2ModelPresenter, BTOR2ModelPresenter
from lib.model_data import (
    ModelData,
    SMT2ModelData,
    BTOR2ModelData,
    BasicModelData,
    SolverRunData,
    GenerationModelData,
)
from lib.presenter import BasePresenter

import lib.config as cfg


class Model:
    """Base model class providing common functionality."""

    def __init__(self, model_config: ModelBaseConfig, data: ModelData, presenter: BasePresenter):
        # At this point output must be generated already
        if not model_config.get_model_path().exists():
            raise ValueError(
                f"Can not create model object from {model_config.get_model_path()}, path does not exists"
            )

        self._data = data
        self._presenter = presenter

    def show(self):
        self._presenter.show(cfg.verbose)

    @property
    def data(self) -> ModelData:
        """Main data access point."""
        return self._data

    # Shortcut: model["key"] -> model.data["key"]
    def __getitem__(self, key):
        return self.data[key]

    def add_solver_data(self, data: SolverRunData):
        if data.success:
            if not self._data.best_run:
                self._data.best_run = data
            else:
                if data.elapsed_time < self._data.best_run.elapsed_time:
                    self._data.best_run = data
        self._data.solver_runs.append(data)


class SMT2Model(Model):
    """SMT-LIBv2 model with parsing and visualization support."""

    def __init__(self, model_config: ModelBaseConfig):
        data = SMT2ModelData(
            basic=BasicModelData.generate(model_config),
            parsed=SMT2ModelParser(model_config.get_model_path()).parse(),
            generation=(
                GenerationModelData.generate(model_config)
                if isinstance(model_config, ModelGenerationConfig)
                else None
            ),
            solver_runs=[],
            best_run=None,
        )
        super().__init__(model_config, data, SMT2ModelPresenter(self))


class BTOR2Model(Model):
    """BTOR2 model placeholder (future implementation)."""

    def __init__(self, model_config: ModelBaseConfig):
        data = BTOR2ModelData(
            basic=BasicModelData.generate(model_config),
            parsed=None,
            generation=(
                GenerationModelData.generate(model_config)
                if isinstance(model_config, ModelGenerationConfig)
                else None
            ),
            solver_runs=[],
            best_run=None,
        )
        super().__init__(model_config, data, BTOR2ModelPresenter(self))

    # TODO


allowed_models = {"smt2": SMT2Model, "btor2": BTOR2Model}

# Assert that cfg.config["allowed_languages"] contains exactly the same keys as allowed_models
assert set(cfg.config["allowed_formats"]) == set(allowed_models.keys())


def model_factory(model_config: ModelBaseConfig):
    """
    Creates the appropriate Model subclass based on format.
    
    Args:
        model_config: Configuration specifying model type and location
        
    Returns:
        Initialized Model instance
        
    Raises:
        ValueError: For unsupported model formats
    """
    format_name = model_config.format
    if format_name not in allowed_models:
        raise ValueError(
            f"Unknown model format: {format_name}. Available: {list(allowed_models.keys())}"
        )
    model_class = allowed_models[model_config.format]
    return model_class(model_config)
