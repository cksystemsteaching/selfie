from lib.presenter import BTRunPresenter

from typing import List, Dict, Any, Optional

def present_overview(models, solvers):
    from lib.presenter import OutputFormat
    from lib.config import verbose

    overview = BTOverview(models, solvers).get_overview()
    presenter = BTRunPresenter(overview)
    presenter.show(format=OutputFormat.VERBOSE if verbose else OutputFormat.PLAIN)

class BTOverview():
    def __init__(self, models, solvers):
        self.models = models
        self.solvers = solvers
    
    def get_overview(self) -> Dict[str, Any]:
        """Return a comprehensive overview of benchmark results."""
        return {
            "models" : self.models,
            "generated_models": self._generated_models(),
            "loaded_models": self._loaded_models(),
            "solved_models": self._solved_models(),
            "used_solvers": self._used_solvers(),
            "best_solver": self._best_solver(),
            "worst_solver": self._worst_solver(),
            "solve_rates": self._solve_rates()
        }

    def _generated_models(self) -> List['Model']:
        """Return models marked as generated."""
        return [model for model in self.models if model.data.generation]

    def _loaded_models(self) -> List['Model']:
        """Return models not marked as generated (assumed loaded)."""
        return [model for model in self.models if not model.data.generation]

    def _solved_models(self) -> List['Model']:
        """Return all successfully solved models across all solvers."""
        solved = set()
        for solver in self.solvers:
            solved.update(model for model in solver.data.solved_models)
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
            key=lambda s: (len(s.data.solved), -s.data.avg_solve_time)  # Prioritize solve count, then speed
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
            key=lambda s: (len(s.data.solved), -s.data.avg_solve_time)  # Prioritize solve count, then speed
        )
        return {
            "name": worst.get_solver_name(),
            "solved": len(worst.data.solved),
            "avg_time": f"{worst.data.avg_solve_time:.2f}s",
        }  

    def _solve_rates(self) -> float:
        """Calculate percentage of models solved by at least one solver."""
        solve_rates = {}
        for solver in self.solvers:
            solved_count = len(solver.data.solved)
            solve_rates.update(solver.get_solver_name(), (solved_count / len(self.models)) * 100)

        return solve_rates