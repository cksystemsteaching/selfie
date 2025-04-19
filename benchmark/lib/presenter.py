import lib.exceptions as ex

from abc import ABC, abstractmethod
from pathlib import Path
from enum import Enum, auto
import logging

class OutputFormat(Enum):
    """Supported output formats"""
    PLAIN = auto()
    VERBOSE = auto()
class BasePresenter(ABC):
    """ Abstract base class for model presenters"""

    def __init__(self):
        self.logger = logging.getLogger(f"bt.{self.__class__.__name__.lower()}")

    def show(self, 
             verbose: bool = True,
             format: OutputFormat = OutputFormat.PLAIN):
        """
        Standardized presentation flow (shared by all presenters)
        """
        output = self._generate_output(format, verbose)
        self.logger.info(output)

    @abstractmethod
    def _generate_plain(self) -> str:
        """Generate plain output (implemented by subclasses)"""
        pass
    
    @abstractmethod
    def _generate_verbose(self) -> str:
        """Generate verbose output (implemented by subclasses)"""
        pass

    def _generate_output(self, format: OutputFormat, verbose: bool) -> str:
        """Shared output generator (can be overridden if needed)"""
        if format == OutputFormat.VERBOSE:
            return self._generate_verbose()
        elif format == OutputFormat.PLAIN:
            return self._generate_plain()
        raise ex.UnreachableError(format, list(OutputFormat))
        
    
    @staticmethod
    def _section(title: str, items: list[str]) -> str:
        """Shared section formatter"""
        lines = [f" {title} ".center(40, "-")]
        lines.extend(items)
        return "\n".join(lines)
    
    @staticmethod
    def _write_output(content: str, path: Path):
        """Shared file writer"""
        path.parent.mkdir(parents=True, exist_ok=True)
        with open(path, 'w') as f:
            f.write(content)


class BTRunPresenter(BasePresenter):
    """Handles presentation of the whole program run"""

    def __init__(self, models):
        super().__init__()
        self.models = models

    def _generate_plain(self):
        # generated = [generated_models for generated_models in self.models if generated_models.data.generation]
        # loaded = [loaded_models for loaded_models in self.models if not loaded_models.data.generation]
        # solved = [solved for solved in self.models if loaded_models.data. ]
        # timed_out = 
        lines = [
            f"Number of models: {len(self.models)}",
            # f"Number of generated models: {len(generated)}",
    
            # f"Number of loaded models: {len(loaded)}"
        ]
        return "\n".join(lines)

class SolverPresenter(BasePresenter):
    """Handles presentation of a specific solver"""

    def __init__(self, solver):
        super().__init__()
        self.solver = solver
    
    def _generate_plain(self):
        lines = [
            f"{self.solver.get_solver_name()} Solver Data",
            f"Total runs: {self.solver.data.runs}",
            f"  Solved runs: {len(self.solver.data.solved)}",
            f"  Timed out runs: {len(self.solver.data.timedout)}",
            f"  Error runs: {len(self.solver.data.error)}",
            f"Average solving time: {self.solver.data.avg_solve_time}",
        ]
        if len(self.solver.data.solved) > 0:
            lines.extend([
                "\nRuns:",
                f"Longest run: {self.solver.data.longest_run[0]}",
                f"  Model: {self.solver.data.longest_run[1]['basic']['output_path']}",
                f"Shortest run: {self.solver.data.shortest_run[0]}",
                f"  Model: {self.solver.data.shortest_run[1]['basic']['output_path']}",
            ])

        return "\n".join(lines)
    
    def _generate_verbose(self):
        """Generate rich verbose output with borders"""
        width = 70
        header = f" {self.solver.get_solver_name()} SOLVER ".center(width, "=")
        footer = "=" * width
        
        sections = [
            self._section("Basic Data", [
                f"Total runs: {self.solver.data.runs}",
                f"  Solved runs: {len(self.solver.data.solved)}",
                f"  Timed out runs: {len(self.solver.data.timedout)}",
                f"  Error runs: {len(self.solver.data.error)}",
                f"Average solving time: {self.solver.data.avg_solve_time}",
            ])
        ]
        if len(self.solver.data.solved) > 0:
            sections.append(
            self._section("Runs", [
                f"Longest run: {self.solver.data.longest_run[0]:.2f}",
                f"  Model: {self.solver.data.longest_run[1]['basic']['output_path']}",
                f"Shortest run: {self.solver.data.shortest_run[0]:.2f}",
                f"  Model: {self.solver.data.shortest_run[1]['basic']['output_path']}",
            ]))

        return f"\n{header}\n" + "\n\n".join(sections) + f"\n{footer}\n"
    
#TODO
class BTORModelPresenter(BasePresenter):
    pass


class SMT2ModelPresenter(BasePresenter):
    """Handles rich presentation of model information for CLI output"""
    
    def __init__(self, model):
        super().__init__()
        self.model = model
    
    def _generate_plain(self) -> str:
        """Generate plain text output"""
        lines = [
            f"Model: {self.model.data.basic.output_path}",
            f"Type: {self.model.__class__.__name__}",
            f"Code lines: {self.model.data.parsed['code_lines']}",
        ]
        
        lines.extend([
            "",
            "Parsed data:",
            f"Total lines: {self.model['parsed']['total_lines']}",
            f"Code lines: {self.model['parsed']['code_lines']}",
            f"Comments: {self.model['parsed']['comment_lines']}",
            f"Blank lines: {self.model['parsed']['blank_lines']}",
            f"Define-fun commands: {self.model['parsed']['define_count']}",
            f"Transitions: {self.model['parsed']['transitions']}",
            f"Rotor generated: {self.model['parsed']['is_rotor_generated']}"
        ])
        
        if self.model['parsed']['is_rotor_generated']:
            lines.append("\nRotor Configuration:")
            lines.extend(self._format_rotor_data())

        if self.model['generation'] != None:
                lines.append("\nGeneration data")
                lines.extend(self._format_generation_data())
        
        #New line at the end
        lines.append("")
        return "\n".join(lines)
    
    def _generate_verbose(self) -> str:
        """Generate rich verbose output with borders"""
        width = 70
        header = f" MODEL ANALYSIS ".center(width, "=")
        footer = "=" * width
        
        sections = [
            self._section("Basic Data", [
                f"File: {self.model.data.basic.name}",
                f"Path: {self.model.data.basic.output_path}",
                f"Type: {self.model.__class__.__name__}",
                f"Format: {self.model.data.basic.format}",
            ]),
            
            self._section("Parsed Data", [
                f"Total lines: {self.model['parsed']['total_lines']}",
                f"Code lines: {self.model['parsed']['code_lines']}",
                f"Comments: {self.model['parsed']['comment_lines']}",
                f"Blank lines: {self.model['parsed']['blank_lines']}",
                f"Define-fun commands: {self.model['parsed']['define_count']}",
                f"Transitions: {self.model['parsed']['transitions']}",
                f"Rotor generated: {self.model['parsed']['is_rotor_generated']}"
            ]),
        ]
        
        if self.model['parsed']['is_rotor_generated']:
            sections.append(
                self._section("Rotor Configuration", self._format_rotor_data())
            )

        if self.model['generation'] != None:
            sections.append(
                self._section("Generation data", self._format_generation_data())
            )
        idx = 1
        for solver_run in self.model.data.solver_runs:
            sections.append(
                self._section(f"Solver run #{idx}", self._format_solver_run_data(solver_run))
            )
            idx+=1


        return f"\n{header}\n" + "\n\n".join(sections) + f"\n{footer}\n"
    
    def _format_rotor_data(self) -> list[str]:
        """Format Rotor-specific model data"""
        header = self.model['parsed']['rotor_data']
        return [
            f"Source: {header.source_file}",
            f"kMin: {header.kmin}, kMax: {header.kmax}",
            f"Bytecode size: {header.bytecode_size} bytes",
            f"Data Size: {header.data_size} bytes",
            f"Virtual Address Space: {header.virtual_address_space}-bit",
            f"Code Size: {header.code_word_size} bytes",
            f"Memory word size: {header.memory_word_size}",
            f"Heap allowance: {header.heap_allowance}",
            f"Stack allowance: {header.stack_allowance}",
            f"Cores: {header.cores}",
            f"Bytes to read: {header.bytestoread}",
            f"Comments removed: {header.comments_removed}",
            f"Flags: {', '.join(header.flags) if header.flags else 'None'}",
        ]
    
    def _format_generation_data(self) -> list[str]:
        """Format model generation related data"""
        data = self.model.data.generation
        return [
            f"Model generation command: {data.model_generation_cmd}",
            f"Model type: {data.model_type}",
            f"Compilation command: {data.compilation_cmd or 'Compiled by Rotor.'}",
        ]
    
    def _format_solver_run_data(self,solver_run):
        return [
            f"Solver: {solver_run.solver_used}",
            f"Command: {solver_run.solver_cmd}",
            f"Elapsed_time: {solver_run.elapsed_time}",
            f"Return code: {solver_run.returncode}",
            f"Success: {solver_run.success}",
            f"Timed_out: {solver_run.timed_out}"
        ]