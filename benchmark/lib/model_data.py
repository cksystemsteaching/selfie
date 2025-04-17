from lib.dict_mixin import DictMixin

from dataclasses import dataclass, fields
from typing import Optional, List

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
            format= model_base_config.format
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
    def generate(model_generation_config : 'ModelGenerationConfig'):
        return GenerationModelData(
            model_generation_config.model_type.model_base,
            model_generation_config.compilation_cmd,
            model_generation_config.model_generation_cmd
        ) 
        
        
@dataclass
class ParsedSMT2ModelData(DictMixin):

    total_lines: Optional[int] = None
    comment_lines: Optional[int] = None
    code_lines: Optional[int] = None
    blank_lines: Optional[int] = None
    define_count: Optional[int]= None
    transitions: Optional[int] = None
    is_rotor_generated: Optional[bool] = None
    rotor_data: Optional[RotorModelData] = None
    
    @staticmethod
    def generate(parser: 'SMT2ModelParser'):
        vals = parser.parse()
        return ParsedSMT2ModelData(
            total_lines=vals["total_lines"],
            comment_lines=vals["comment_lines"],
            code_lines=vals["code_lines"],
            blank_lines=vals["blank_lines"],
            define_count=vals["define_count"],
            transitions=vals["transitions"],
            is_rotor_generated=vals["is_rotor_generated"],
            rotor_data=vals.get("rotor_header"),
        )

@dataclass
class ParsedBTOR2ModelData(DictMixin):
    _parser: 'BTOR2ModelParser'

    #TODO

@dataclass
class SolverRunData(DictMixin):
    solver_used: str
    solver_cmd: str
    elapsed_time: int
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
class SMT2ModelData(DictMixin):
    basic: BasicModelData
    # Model can also be loaded, thus missing the generation data
    generation: Optional[GenerationModelData]
    parsed: ParsedSMT2ModelData
    # Model can undergo several solvings from different solvers
    solver_runs: List[SolverRunData]

@dataclass
class BTOR2ModelData(DictMixin):
    basic: BasicModelData
    # Model can also be loaded, thus missing the generation data
    generation: Optional[GenerationModelData]
    parsed: ParsedBTOR2ModelData
    # Model can undergo several solvings from different solvers
    solver_runs: List[SolverRunData]