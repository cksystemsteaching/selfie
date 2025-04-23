from lib.dict_mixin import DictMixin

from dataclasses import dataclass, fields, field
from typing import Optional, List, List, Tuple


@dataclass
class BasicModelData(DictMixin):
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
    source_file: Optional[str] = None
    kmin: Optional[int] = None
    kmax: Optional[int] = None
    bytecode_size: Optional[int] = None
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
    model_type: str
    compilation_cmd: str
    model_generation_cmd: str

    @staticmethod
    def generate(model_generation_config: "ModelGenerationConfig"):
        return GenerationModelData(
            model_generation_config.model_type.model_base,
            model_generation_config.compilation_cmd,
            model_generation_config.model_generation_cmd,
        )


@dataclass
class ParsedSMT2ModelData(DictMixin):
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
    solver_used: str
    solver_cmd: str
    elapsed_time: float
    returncode: int
    stdout: str
    stderr: str
    success: bool
    timed_out: bool
    error_message: str

    @classmethod
    def from_dict(cls, data: dict):
        valid_fields = {f.name for f in fields(cls)}
        return cls(**{k: v for k, v in data.items() if k in valid_fields})


@dataclass
class SolverData(DictMixin):
    runs: int = 0
    solved: List["Model"] = field(default_factory=list)
    timedout: List["Model"] = field(default_factory=list)
    error: List["Model"] = field(default_factory=list)
    avg_solve_time: float = float("inf")
    longest_run: Tuple[float, "Model"] = (0.0, None)
    shortest_run: Tuple[float, "Model"] = (float("inf"), None)


@dataclass
class SMT2ModelData(DictMixin):
    basic: BasicModelData
    # Model can also be loaded, thus missing the generation data
    generation: Optional[GenerationModelData]
    parsed: ParsedSMT2ModelData
    # Model can undergo several solvings from different solvers
    solver_runs: List[SolverRunData]
    best_run: SolverRunData


@dataclass
class BTOR2ModelData(DictMixin):
    basic: BasicModelData
    # Model can also be loaded, thus missing the generation data
    generation: Optional[GenerationModelData]
    parsed: ParsedBTOR2ModelData
    # Model can undergo several solvings from different solvers
    solver_runs: List[SolverRunData]
    best_run: SolverRunData
