"""
Presenting information stored in data classes throughout the run to the user.
"""
from abc import ABC, abstractmethod
from pathlib import Path
import logging

class BasePresenter(ABC):
    """ Abstract base class for model presenters"""

    def __init__(self):
        self.logger = logging.getLogger(f"bt.{self.__class__.__name__.lower()}")

    def show(self, verbose: bool):
        """
        Standardized presentation flow (shared by all presenters)
        """
        output = self._generate_output(verbose)
        print(output)
        # Also logs into a log file
        logging.getLogger("bt-file.presenter").info(output)

    @abstractmethod
    def _generate_plain(self) -> str:
        """Generate plain output (implemented by subclasses)"""
        pass
    
    @abstractmethod
    def _generate_verbose(self) -> str:
        """Generate verbose output (implemented by subclasses)"""
        pass

    def _generate_output(self, verbose: bool) -> str:
        """Shared output generator (can be overridden if needed)"""
        if verbose:
            return self._generate_verbose()
        else:
            return self._generate_plain()
        
    
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

    def __init__(self, overview: 'BTOverview'):
        super().__init__()
        self.overview = overview

    def _generate_plain(self):
        lines = [
            "","Models:", *self._models_lines(),
            ]
        if self.overview["smt2"]:
            lines.extend(["SMT2 Models:", *self._smt2_model_lines()])

        if self.overview["used_solvers"]:
            lines.extend(["Solvers:", *self._solvers_lines()])

        return "\n".join(lines)
    
    def _generate_verbose(self) -> str:
        """Generate rich verbose output with borders and formatted sections."""
        width = 70
        header = " BT Overview ".center(width, "=")
        footer = "=" * width

        sections = [
            self._section("All Models", self._models_lines()),
        ]

        if self.overview["smt2"]:
            sections.append(self._section("SMT2 Models", self._smt2_model_lines()))

        if self.overview["used_solvers"]:
            sections.append(self._section("Solvers", self._solvers_lines()))

        return f"\n{header}\n" + "\n\n".join(sections) + f"\n{footer}\n"

    def _models_lines(self) -> str:
        """Generate the model-related lines."""
        lines = [
            f"Number of models: {len(self.overview['models'])}",
            f"  Generated models: {len(self.overview['generated_models'])}",
            f"  Loaded models: {len(self.overview['loaded_models'])}",
        ]
        if self.overview['used_solvers']:
            lines.append(f"Solved models: {len(self.overview['solved_models'])}")
        
        return lines
    
    def _smt2_model_lines(self) -> list[str]:
        """Generated model parsing related data"""
        lines = [
            f"Number of models: {len(self.overview['smt2']['models'])}",
            f"Average check-sats per line: {self.overview['smt2']['avg_check_sats_per_line']:2f}",
            f"Average declarations per line: {self.overview['smt2']['avg_declarations_per_line']:2f}",
            f"Average definitions per line: {self.overview['smt2']['avg_definitions_per_line']:2f}",
            f"Average assertions per check-sat: {self.overview['smt2']['avg_assertions_per_check_sat']:2f}",
        ]
        return lines

    def _solvers_lines(self) -> list[str]:
        """Generate solver-related lines."""        
        lines = [
            f"Used solvers: {','.join(self.overview['used_solvers'])}",
            *self._format_solve_rates()
        ]
        if len(self.overview["used_solvers"]) > 1:
            lines.extend([
                *self._format_best_worst_solver(best=True, solver=self.overview['best_solver']),
                *self._format_best_worst_solver(best=False, solver=self.overview['worst_solver']),
            ])
        return lines
    
    def _format_best_worst_solver(self, best: bool, solver) -> list[str]:
        lines = []
        if best:
            lines.append(f"Best solver: {solver['name']}")
        else:
            lines.append(f"Worst solver: {solver['name']}")
        
        lines.extend([
            f"  Solved: {solver['solved']}",
            f"  Average solving time: {solver['avg_time']}",
        ])
        return lines

    def _format_solve_rates(self) -> list[str]:
        lines = ["Solve rates:"]
        for rate in self.overview['solve_rates'].items():
            lines.append(f"  {rate[0]}: {rate[1]}")
        return lines

class SolverPresenter(BasePresenter):
    """Handles presentation of solver results with consistent formatting."""
    
    def __init__(self, solver: 'BaseSolver'):
        super().__init__()
        self.solver = solver

    def _generate_plain(self) -> str:
        """Generate simple text output."""
        lines = [
            f"{self.solver.get_solver_name()} Solver Data",
            *self._format_basic(),
            *self._format_important_runs()
        ]
        return "\n".join(filter(None, lines))  # Skip empty lines
    
    def _generate_verbose(self) -> str:
        """Generate rich formatted output with borders."""
        width = 70
        header = f" {self.solver.get_solver_name()} Solver ".center(width, "=")
        footer = "=" * width
        
        sections = [
            self._section("Basic Data", self._format_basic()),
            self._section("Runs", self._format_important_runs())
        ]
        
        return f"\n{header}\n" + "\n\n".join(filter(None, sections)) + f"\n{footer}\n"
    
    def _format_basic(self) -> list[str]:
        """Generate lines for basic statistics section."""
        return [
            f"Total runs: {self.solver.data.runs}",
            f"  Solved runs: {len(self.solver.data.solved)}",
            f"  Timed out runs: {len(self.solver.data.timedout)}",
            f"  Error runs: {len(self.solver.data.error)}",
            f"Average solving time: {self.solver.data.avg_solve_time:.4f}",
        ]

    def _format_important_runs(self) -> list[str]:
        """Generate lines for run statistics section."""
        if not len(self.solver.data.solved) > 0:
            return []
            
        return [
            "\nRuns:",
            f"Longest run: {self.solver.data.longest_run[0]:.2f}",
            f"  Model: {self.solver.data.longest_run[1].data.basic.output_path}",
            f"Shortest run: {self.solver.data.shortest_run[0]:.2f}",
            f"  Model: {self.solver.data.shortest_run[1].data.basic.output_path}",
        ]
    
#TODO
class BTOR2ModelPresenter(BasePresenter):
    def __init__(self, model: 'BTOR2Model'):
        super().__init__()
        self.model = model
    
    def _generate_plain(self) -> str:
        """Generate plain text output"""
        lines = [
            f"Model: {self.model.data.basic.output_path}",
            f"Type: {self.model.__class__.__name__}",
        ]
        #New line at the end
        lines.append("")
        return "\n".join(lines)

    def _generate_verbose(self):
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
        ]

        return f"\n{header}\n" + "\n\n".join(sections) + f"\n{footer}\n"

class SMT2ModelPresenter(BasePresenter):
    """Handles rich presentation of model information for CLI output"""
    
    def __init__(self, model: 'SMT2Model'):
        super().__init__()
        self.model = model

    def _generate_plain(self) -> str:
        """Generate plain text output"""
        lines = self._format_basic_data()
        
        lines.extend(self._format_parsed_data())
        
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
            self._section("Basic Data", self._format_basic_data()),
            
            self._section("Parsed Data", self._format_parsed_data()),
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
        
        if self.model.data.best_run and len(self.model.data.solver_runs) > 1:
            sections.append(
                self._section(f"Best solver run", self._format_solver_run_data(self.model.data.best_run))
            )

        return f"\n{header}\n" + "\n\n".join(sections) + f"\n{footer}\n"

    def _format_basic_data(self):
        return [
                f"File: {self.model.data.basic.name}",
                f"Path: {self.model.data.basic.output_path}",
                f"Type: {self.model.__class__.__name__}",
                f"Format: {self.model.data.basic.format}",
            ]
    
    def _format_parsed_data(self):
         return [
            "\nParsed data:",
            f"Total lines: {self.model['parsed']['total_lines']}",
            f"  Code lines: {self.model['parsed']['code_lines']}",
            f"  Comments lines: {self.model['parsed']['comment_lines']}",
            f"  Blank lines: {self.model['parsed']['blank_lines']}",
            f"Commands:",
            f"  Declarations: {self.model['parsed']['definition']}",
            f"  Definitions: {self.model['parsed']['declaration']}",
            f"  Assertions: {self.model['parsed']['assertion']}",
            f"  Push commands: {self.model['parsed']['push']}",
            f"  Pop commands: {self.model['parsed']['pop']}",
            f"  Check-sat commands: {self.model['parsed']['check_sat']}",
            f"  Other commands: {self.model['parsed']['other_commands']}",
            f"Rotor generated: {self.model['parsed']['is_rotor_generated']}"
        ]
    def _format_rotor_data(self) -> list[str]:
        """Format Rotor-specific model data"""
        header = self.model['parsed']['rotor_data']
        return [
            f"Source: {header.source_file}",
            f"kMin: {header.kmin}, kMax: {header.kmax}",
            f"Source Code size: {header.source_code_size} bytes",
            f"Source Data Size: {header.data_size} bytes",
            f"Virtual Address Space: {header.virtual_address_space}-bit",
            f"Code Word Size: {header.code_word_size} bytes",
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
        lines = [
            f"Solver: {solver_run.solver_used}",
            f"Command: {solver_run.solver_cmd}",
            f"Elapsed time: {solver_run.elapsed_time:.02f}",
            f"Return code: {solver_run.returncode}",
            f"Success: {solver_run.success}",
            f"Timed out: {solver_run.timed_out}",
            f"Max RSS: {solver_run.max_rss} MB",
            f"Max CPU usage: {solver_run.max_cpu_percent}%",

        ]
        if solver_run.error_message:
            lines.append(
                f"Error message: {solver_run.error_message}"
            )
        return lines