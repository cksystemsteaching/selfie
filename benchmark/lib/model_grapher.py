"""
Model visualization system with:
- Format-specific graphing (SMT2/BTOR2)
- Professional styling and layouts
- Statistical analysis integration

Hierarchy:
1. GrapherWrapper - Distributes models and coordinates output
2. ModelGrapher (ABC) - Base class with shared utilities
3. SMT2ModelGrapher - Implements SMT2-specific visualizations
4. BTOR2ModelGrapher - Placeholder for future BTOR2 support
"""

import lib.config as cfg
from lib.exceptions import ConfigFormatError
from lib.color_map import ColorMap

from abc import ABC, abstractmethod
import matplotlib.pyplot as plt
import numpy as np
import logging


class GrapherWrapper:
    """Orchestrates model distribution and graph generation.
    
    Key Features:
    - Validates model formats against config
    - Creates format-specific output directories
    - Delegates to specialized graphers
    """
    def __init__(self, output_path, models):
        self.output_path = output_path if output_path.is_dir() else output_path.parent()
        self.models = models  # Store models as instance variable
        self.graphers = self._initialize_graphers()  # Initialize and validate
        self._distribute_models()

    def _initialize_graphers(self):
        """Initialize and validate format-specific graphers."""
        graphers = {"smt2": SMT2ModelGrapher(), "btor2": BTOR2ModelGrapher()}

        # Validate all required formats exist
        for fmt in cfg.config["allowed_formats"]:
            if fmt not in graphers:
                raise ConfigFormatError(
                    message=f"Format '{fmt}' is not implemented",
                    error_format=fmt,
                    provided_formats=list(graphers.keys()),
                    class_name=self.__class__.__name__,
                    method="_initialize_graphers",
                )
        return graphers

    def _distribute_models(self):
        """Distribute models to their respective graphers."""
        for model in self.models:
            try:
                self.graphers[model.data.basic.format].add(model)
            except KeyError as e:
                raise ValueError(
                    f"Model format {model.data.basic.format} not in "
                    f"allowed formats: {list(self.graphers.keys())}"
                ) from e

    def generate_graphs(self):
        """Generate and save all graphs."""

        for fmt, grapher in self.graphers.items():
            if grapher.models:
                output_dir = self.output_path._path / (fmt + "_graphs")
                output_dir.mkdir(exist_ok=True)
                grapher.save_figures(output_dir)


class ModelGrapher(ABC):
    """Abstract base class providing:
    - Consistent styling (colors, fonts, grids)
    - Multi-figure generation pipeline
    - Standardized saving/display methods
    """

    def __init__(self):
        self.models = []
        self.logger = logging.getLogger(f"bt.{self.__class__.__name__.lower()}")
        self._setup_style()

    def _setup_style(self):
        """Shared style configuration for all figures"""
        plt.style.use("seaborn-v0_8-whitegrid")
        self.colors = {
            "primary": "#4C72B0",
            "secondary": "#55A868",
            "highlight": "#E24A33",
            "text": "#555555",
            "bars": "#555555",
            "avg_line": "#FFFFFF",
        }
        self.figsize = (10, 6)

    @abstractmethod
    def generate_all_figures(self):
        """Generate all standard figures for this model type"""
        pass

    def save_figures(self, output_path):
        """Save all generated figures"""
        for fig_name, fig in self.generate_all_figures().items():
            path = output_path / f"{fig_name}.png"
            fig.savefig(path, dpi=300, bbox_inches="tight")
            plt.close(fig)
            self.logger.info(f"Saved {fig_name} to {path}")

    @abstractmethod
    def show(self):
        pass

    def add(self, model):
        self.models.append(model)


class SMT2ModelGrapher(ModelGrapher):
    def __init__(self):
        super().__init__()

    def show(self):
        """Display the graph interactively"""
        self.generate_all_figures()
        plt.show()

    def generate_all_figures(self) -> dict[str, plt.Figure]:
        """Generate standard battery of SMT2 analysis figures"""
        if not self.models:
            return
        return {
            "line_counts": self._create_line_count_figure(),
            "define_distribution": self._create_define_figure(),
            "metrics_per_line": self._create_avg_metrics_per_line_figure(),
        }

    def _create_line_count_figure(self):
        """Core graphing logic"""
        colors = {
            "bars": ColorMap.PRIMARY["blue"],
            "avg_line": ColorMap.PRIMARY["red"],
            "text": "#333333",
            "outliers": ColorMap.PRIMARY["orange"],
        }
        # Prepare data
        names = [m.data.basic.name for m in self.models]
        line_counts = [m.data.parsed.total_lines for m in self.models]
        avg_lines = np.mean(line_counts)

        # Create figure
        fig, ax = plt.subplots(figsize=self.figsize)

        # Bar plot
        bars = ax.bar(
            names, line_counts, color=colors["bars"], width=0.7, edgecolor="white"
        )

        # Average line
        ax.axhline(
            avg_lines,
            color=colors["avg_line"],
            linestyle="--",
            linewidth=2,
            label=f"Average ({avg_lines:.1f} lines)",
        )

        # Value labels
        for bar in bars:
            height = bar.get_height()
            ax.text(
                bar.get_x() + bar.get_width() / 2.0,
                height,
                f"{height}",
                ha="center",
                va="bottom",
                color=colors["text"],
            )
        # Rotate long names
        if max(len(name) for name in names) > 8:
            plt.xticks(rotation=45, ha="right")

        self._format_axes(ax, fig, "Model Line Counts", "Model Name", "Total Lines")
        return fig

    def _create_define_figure(self) -> plt.Figure:
        """Figure 2: Define command distribution with regression analysis

        Creates a scatter plot showing the relationship between code size (lines)
        and define commands, with:
        - Automatic trend line
        - Confidence interval
        - Annotated statistics
        - Professional styling
        """
        # Data extraction
        code_lines = [m.data.parsed.code_lines for m in self.models]
        defines = [m.data.parsed.definition for m in self.models]

        # Create figure with constrained layout
        fig, ax = plt.subplots(figsize=self.figsize)

        # Main scatter plot
        scatter = ax.scatter(
            code_lines,
            defines,
            color=self.colors["primary"],
            s=120,  # Slightly larger markers
            edgecolor="white",  # White border for clarity
            linewidth=1,
            alpha=0.8,  # Slight transparency
            zorder=3,  # Ensure points stay on top
        )

        # Add regression line and CI
        try:
            self._add_regression(ax, code_lines, defines)
        except ValueError as e:
            self.logger.info("Skipping regression...")

        # Annotate key stats
        self._annotate_stats(ax, code_lines, defines)

        # Formatting
        self._format_axes(
            ax,
            fig,
            title="Define Command Density Analysis",
            xlabel="Code Lines",
            ylabel="Define Commands",
            grid=True,
        )

        # Add supplemental elements
        ax.spines[["top", "right"]].set_visible(False)
        ax.set_axisbelow(True)  # Grid behind data

        return fig

    def _add_regression(self, ax, x, y, color=None, ci=95, text_pos=(0.05, 0.95)):
        """Add linear regression with confidence interval and R² annotation.

        Args:
            ax: Matplotlib axis object.
            x, y: Data for regression (must be same length).
            color: Color for the regression line.
            ci: Confidence interval (None to disable).
            text_pos: (x, y) position for R² text (axes coordinates).

        Raises:
            ValueError: If input data is invalid.
        """
        import numpy as np
        import seaborn as sns
        from scipy import stats

        # Convert to numpy arrays and remove NaN/Inf
        x = np.asarray(x, dtype=np.float64)
        y = np.asarray(y, dtype=np.float64)

        mask = np.isfinite(x) & np.isfinite(y)
        x_clean = x[mask]
        y_clean = y[mask]

        if len(x_clean) < 2:
            raise ValueError("Not enough finite data points for regression.")

        if np.all(x_clean == x_clean[0]):
            raise ValueError("All x-values are identical (zero variance).")

        # Proceed only with clean data
        if not color:
            color = self.colors.get("highlight", "tab:blue")

        sns.regplot(
            x=x_clean,
            y=y_clean,
            scatter=False,
            color=color,
            line_kws={"lw": 2.5, "zorder": 2},
            ci=ci,
            ax=ax,
        )

        slope, intercept, r_value, _, _ = stats.linregress(x_clean, y_clean)
        ax.text(
            *text_pos,
            f"R² = {r_value**2:.2f}",
            transform=ax.transAxes,
            ha="left",
            va="top",
            bbox=dict(facecolor="white", alpha=0.8, edgecolor="none"),
        )

    def _annotate_stats(self, ax, x, y):
        """Add key statistical annotations"""
        avg_ratio = np.mean(np.array(y) / np.array(x))

        ax.axhline(
            np.mean(y),
            color=self.colors["secondary"],
            linestyle=":",
            label=f"Mean Defines: {np.mean(y):.1f}",
        )

        ax.axline(
            (0, 0),
            slope=avg_ratio,
            color=self.colors["text"],
            linestyle="--",
            alpha=0.5,
            label=f"Avg Ratio: {avg_ratio:.2f} defines/line",
        )

        ax.legend(frameon=True, framealpha=0.9, loc="upper left")

    def _format_axes(
        self,
        ax: plt.Axes,
        fig: plt.Figure,
        title: str,
        xlabel: str,
        ylabel: str,
        grid: bool = True,
        tick_style: str = "default",
    ) -> None:
        """Professional axes formatting with grid support

        Args:
            ax: Matplotlib axes object
            fig: Matplotlib figure object
            title: Axis title
            xlabel: X-axis label
            ylabel: Y-axis label
            grid: Whether to show grid (default: True)
            tick_style: 'default' or 'scientific'
        """
        # Title and labels
        ax.set_title(title, pad=15, fontsize=14, weight="semibold")
        ax.set_xlabel(xlabel, labelpad=10, fontsize=12)
        ax.set_ylabel(ylabel, labelpad=10, fontsize=12)

        # Grid configuration
        if grid:
            ax.grid(
                True,
                which="major",
                linestyle="-",
                linewidth=0.5,
                color="#E0E0E0",
                zorder=0,
            )
            ax.grid(
                True,
                which="minor",
                linestyle=":",
                linewidth=0.3,
                color="#F0F0F0",
                zorder=0,
            )

        # Tick formatting
        ax.tick_params(axis="both", which="both", labelsize=10)
        if tick_style == "scientific":
            ax.ticklabel_format(
                style="sci", axis="both", scilimits=(0, 0), useMathText=True
            )
            ax.yaxis.offsetText.set_fontsize(10)
            ax.xaxis.offsetText.set_fontsize(10)

        # Rotate ticks if crowded
        if len(ax.get_xticklabels()) > 6:
            plt.setp(
                ax.get_xticklabels(), rotation=45, ha="right", rotation_mode="anchor"
            )

        # Adjust layout
        fig.tight_layout()
        fig.set_facecolor("white")
        ax.set_facecolor("white")

        # Set axis spines
        for spine in ax.spines.values():
            spine.set_edgecolor("#888888")
            spine.set_linewidth(0.8)

    def _create_avg_metrics_per_line_figure(self) -> plt.Figure:
        """Create a figure showing average metrics per line across all models.

        Shows average check-sat, declarations, and definitions per line as bars.
        Y-axis capped at 1 for easy comparison.
        """
        # Prepare data - calculate averages
        metrics = {
            "check-sat": np.mean(
                [m.data.parsed.check_sats_per_line() for m in self.models]
            ),
            "declarations": np.mean(
                [m.data.parsed.declarations_per_line() for m in self.models]
            ),
            "definitions": np.mean(
                [m.data.parsed.definitions_per_line() for m in self.models]
            ),
        }

        # Color setup
        colors = {
            "check-sat": ColorMap.PRIMARY["blue"],
            "declarations": ColorMap.PRIMARY["green"],
            "definitions": ColorMap.PRIMARY["orange"],
        }

        # Create figure
        fig, ax = plt.subplots(
            figsize=(8, 6)
        )  # Slightly smaller figure for single chart

        # Plot each metric
        x = np.arange(len(metrics))
        bars = ax.bar(
            x,
            metrics.values(),
            width=0.6,
            color=[colors[k] for k in metrics.keys()],
            edgecolor="white",
        )

        # Set x-axis labels
        ax.set_xticks(x)
        ax.set_xticklabels([k.capitalize() for k in metrics.keys()])

        # Set y-axis limit
        ax.set_ylim(0, min(1, max(metrics.values()) * 1.2))  # Auto-adjust if max < 1

        # Add value labels
        for bar in bars:
            height = bar.get_height()
            ax.text(
                bar.get_x() + bar.get_width() / 2.0,
                height + 0.01,
                f"{height:.3f}",
                ha="center",
                va="bottom",
                color="#333333",
            )

        # Add model count annotation
        ax.text(
            0.95,
            0.95,
            f"n = {len(self.models)} models",
            transform=ax.transAxes,
            ha="right",
            va="top",
            bbox=dict(facecolor="white", alpha=0.8, edgecolor="none"),
        )

        self._format_axes(
            ax,
            fig,
            title="Average SMT2 Metrics per Code Line",
            xlabel="Metric Type",
            ylabel="Average Value (per line)",
            grid=True,
        )

        return fig


class BTOR2ModelGrapher(ModelGrapher):
    """Placeholder for future BTOR2 visualization support."""
    def __init__(self):
        super().__init__()

    def show(self):
        pass

    def generate_all_figures(self):
        """Core graphing logic"""
        return {}
