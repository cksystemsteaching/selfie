"""
Structured model metadata containers with dictionary access (via DictMixin).

Hierarchy:
1. Core Data (Basic/Generation/Rotor)
2. Format-Specific Analysis (SMT2/BTOR2 parsing stats)
3. Solver Results (Individual runs and aggregates)
"""

from lib.dict_mixin import DictMixin

from dataclasses import dataclass, fields, field
from typing import Optional, List, List, Tuple, Dict


@dataclass
class BasicModelData(DictMixin):
    """Essential model identifiers (name, path, format)."""

    name: Optional[str] = None
    output_path: Optional[str] = None
    format: Optional[str] = None

    @staticmethod
    def generate(model_base_config):
        return BasicModelData(
            name=model_base_config.get_model_path().name,
            output_path=model_base_config.get_model_path(),
            format=model_base_config.format,
        )


@dataclass
class RotorModelData(DictMixin):
    """Rotor-specific parameters (memory layout, flags, etc.).
    The parameters need to be parsed from a model."""

    source_file: Optional[str] = None
    kmin: Optional[int] = None
    kmax: Optional[int] = None
    source_code_bytes: Optional[int] = None
    data_size: Optional[int] = None
    virtual_address_space: Optional[int] = None
    code_word_size: Optional[int] = None
    memory_word_size: Optional[int] = None
    heap_allowance: Optional[int] = None
    stack_allowance: Optional[int] = None
    cores: Optional[int] = None
    bytestoread: Optional[int] = None
    flags: List[str] = None
    comments_removed: bool = False


@dataclass
class GenerationModelData(DictMixin):
    """Build process details (commands used for compilation/model generation)."""

    model_type: str
    compilation_cmd: str
    model_generation_cmd: str

    @staticmethod
    def generate(model_generation_config: "ModelGenerationConfig"):
        return GenerationModelData(
            model_generation_config.model_type.name,
            model_generation_config.compilation_cmd,
            model_generation_config.model_generation_cmd,
        )


@dataclass
class ParsedSMT2ModelData(DictMixin):
    """
    SMT2 file analysis results with:
    - Line statistics (code/comments/blanks)
    - Command counts (assertions/checks/declarations)
    - Derived metrics (e.g., assertions_per_check_sat)
    """

    # lines
    total_lines: int = 0
    comment_lines: int = 0
    code_lines: int = 0
    blank_lines: int = 0

    # commands
    declaration: int = 0
    definition: int = 0
    assertion: int = 0
    push: int = 0
    pop: int = 0
    check_sat: int = 0
    other_commands: int = 0

    # rotor info
    is_rotor_generated: bool = False
    rotor_data: Optional[RotorModelData] = None

    def check_sats_per_line(self):
        return self.check_sat / max(1, self.code_lines)

    def declarations_per_line(self):
        return self.declaration / max(1, self.code_lines)

    def definitions_per_line(self):
        return self.definition / max(1, self.code_lines)

    def assertions_per_check_sat(self):
        return self.assertion / max(1, self.check_sat)


@dataclass
class ParsedBTOR2ModelData(DictMixin):
    _parser: "BTOR2ModelParser"

    # TODO


@dataclass
class SolverRunData(DictMixin):
    """Single solver execution results (timing, output, success state).
    - is owned by a Model"""

    solver_used: str = ""
    solver_cmd: str = ""
    elapsed_time: float = 0
    returncode: int = 0
    stdout: str = ""
    stderr: str = ""
    success: bool = False
    timed_out: bool = False
    error_message: str = ""

    max_rss: int = 0  # resident set size in bytes (used RAM)
    max_cpu_percent: int = 0

    @classmethod
    def from_dict(cls, data: dict):
        valid_fields = {f.name for f in fields(cls)}
        return cls(**{k: v for k, v in data.items() if k in valid_fields})

from lib.solver_profile import SolverProfiler
@dataclass
class SolverData(DictMixin):
    """Aggregated solver performance across multiple runs.
    - is owned by a Solver"""

    runs: int = 0
    solved: List["Model"] = field(default_factory=list)
    timedout: List["Model"] = field(default_factory=list)
    error: List["Model"] = field(default_factory=list)
    avg_solve_time: float = 0.0
    longest_run: Tuple[float, "Model"] = (0.0, None)
    shortest_run: Tuple[float, "Model"] = (float("inf"), None)

    profile: SolverProfiler = field(default_factory=SolverProfiler)
@dataclass
class ModelData(DictMixin):
    """
    Essential data for every model not depending on format
    - basic: Core identifiers
    - generation: Build metadata (optional)
    - solver_runs: Benchmark history
    - best_run: Top-performing result
    """

    basic: BasicModelData
    # Model can be loaded, thus missing the generation data
    generation: Optional[GenerationModelData]
    # Model can undergo several solvings from different solvers
    solver_runs: List[SolverRunData]
    best_run: SolverRunData


@dataclass
class SMT2ModelData(ModelData):
    """
    SMT2 model representation:
    - parsed: Structural analysis
    """

    parsed: ParsedSMT2ModelData


@dataclass
class BTOR2ModelData(ModelData):
    parsed: ParsedBTOR2ModelData
