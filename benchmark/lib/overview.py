"""
Overview classes from the run pipeline of the whole BT run. 

Key Components:
1. BTOverview: Hold the most important and non-specific info from the run
2. SMT2Overview: Holds and provides SMT-LIBv2 model specific info from the run
"""

from lib.presenter import BTRunPresenter
from lib.exceptions import UnsupportedModelException
import lib.config as cfg

from typing import List, Dict, Any, Optional


def present_overview(models, solvers):
    overview = BTOverview(models, solvers).get_overview()
    presenter = BTRunPresenter(overview)
    presenter.show(cfg.verbose)


class BTOverview:
    def __init__(self, models, solvers):
        self.models = models
        self.solvers = solvers

    def get_overview(self) -> Dict[str, Any]:
        """Return a comprehensive overview of benchmark results."""
        return {
            # Model data
            "models": self.models,
            "generated_models": self._generated_models(),
            "loaded_models": self._loaded_models(),
            "solved_models": self._solved_models(),
            # Model specific data
            "smt2": SMT2Overview(
                [model for model in self.models if model.data.basic.format == "smt2"]
            ).get_overview(),
            # Solver data
            "used_solvers": self._used_solvers(),
            "best_solver": self._best_solver(),
            "worst_solver": self._worst_solver(),
            "solve_rates": self._solve_rates(),
        }

    def _generated_models(self) -> List["Model"]:
        """Return models marked as generated."""
        return [model for model in self.models if model.data.generation]

    def _loaded_models(self) -> List["Model"]:
        """Return models not marked as generated (assumed loaded)."""
        return [model for model in self.models if not model.data.generation]

    def _solved_models(self) -> List["Model"]:
        """Return all successfully solved models across all solvers."""
        solved = set()
        for solver in self.solvers:
            solved.update(model for model in solver.data.solved)
        return list(solved)

    def _used_solvers(self) -> List[str]:
        """Return names of solvers that were actually used."""
        used_solvers = [s for s in self.solvers if s.data.runs > 0]
        return [solver.get_solver_name() for solver in used_solvers]

    def _best_solver(self) -> Optional[Dict[str, Any]]:
        """Return the solver with the most success runs and best avg time."""
        if not self.solvers:
            return None

        best = max(
            self.solvers,
            key=lambda s: (
                len(s.data.solved),
                -s.data.avg_solve_time,
            ),  # Prioritize solve count, then speed
        )
        return {
            "name": best.get_solver_name(),
            "solved": len(best.data.solved),
            "avg_time": f"{best.data.avg_solve_time:.2f}s",
        }

    def _worst_solver(self) -> Optional[Dict[str, Any]]:
        """Return the solver with the least success runs and best avg time."""
        if not self.solvers:
            return None

        worst = min(
            self.solvers,
            key=lambda s: (
                len(s.data.solved),
                -s.data.avg_solve_time,
            ),  # Prioritize solve count, then speed
        )
        return {
            "name": worst.get_solver_name(),
            "solved": len(worst.data.solved),
            "avg_time": f"{worst.data.avg_solve_time:.2f}s",
        }

    def _solve_rates(self) -> float:
        """Get solve rates for every used solver."""
        solve_rates = {}
        for solver in self.solvers:
            if solver.data.runs > 0:
                solved_count = len(solver.data.solved)
                solve_rates[solver.get_solver_name()] = (
                    solved_count / len(self.models)
                ) * 100

        return solve_rates


class SMT2Overview:
    def __init__(self, models):
        self.models = models

    def check_models(self):
        for model in self.models:
            if model.basic.format != "smt2":
                raise UnsupportedModelException(
                    "SMT Overview received invalid model type {model.basic.format}",
                    model,
                )

    def get_overview(self):
        if not self.models:
            return None
        return {
            "models": self.models,
            "avg_check_sats_per_line": self._avg_check_sat_per_line(),
            "avg_declarations_per_line": self._avg_declaration_per_line(),
            "avg_definitions_per_line": self._avg_definition_per_line(),
            "avg_assertions_per_check_sat": self._avg_assertions_per_check_sat(),
        }

    def _avg_check_sat_per_line(self):
        return sum(
            [model.data.parsed.check_sats_per_line() for model in self.models], 0
        ) / max(1, len(self.models))

    def _avg_declaration_per_line(self):
        return sum(
            [model.data.parsed.declarations_per_line() for model in self.models], 0
        ) / max(1, len(self.models))

    def _avg_definition_per_line(self):
        return sum(
            [model.data.parsed.definitions_per_line() for model in self.models], 0
        ) / max(1, len(self.models))

    def _avg_assertions_per_check_sat(self):
        return sum(
            [model.data.parsed.assertions_per_check_sat() for model in self.models], 0
        ) / max(1, len(self.models))


# TODO
class BTOR2Overview:
    def __init__(self):
        pass
