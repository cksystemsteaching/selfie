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
from lib.solver import available_solvers

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

    def __init__(self, output_path, models, solvers):
        self.output_path = output_path if output_path.is_dir() else output_path.parent()
        self.models = models
        self.solvers = solvers
        self.graphers = self._initialize_graphers()  # Initialize and validate
        self._distribute_data()

    def _initialize_graphers(self):
        """Initialize and validate format-specific graphers."""
        model_graphers = {"smt2": SMT2ModelGrapher(), "btor2": BTOR2ModelGrapher()}
        solver_graphers = {
            "z3": SolverGrapher(),
            "bitwuzla": SolverGrapher(),
            "bitwuzla-py": SolverGrapher(),
        }

        # Validate all required formats exist
        for fmt in cfg.config["allowed_formats"]:
            if fmt not in model_graphers:
                raise ConfigFormatError(
                    message=f"Grapher for model formats:'{fmt}' is not implemented",
                    error_format=fmt,
                    provided_formats=list(model_graphers.keys()),
                    class_name=self.__class__.__name__,
                    method="_initialize_graphers",
                )
        for slv in available_solvers:
            if slv not in solver_graphers:
                raise ConfigFormatError(
                    message=f"Grapher for solver {slv} is not implemented",
                    error_format=slv,
                    provided_solvers=list(available_solvers),
                    class_name=self.__class__.__name__,
                    method="_initialize_graphers",
                )
        return dict(model_graphers, **solver_graphers)

    def _distribute_data(self):
        """Distribute models to their respective graphers."""
        for model in self.models:
            try:
                self.graphers[model.data.basic.format].add(model)
            except KeyError as e:
                raise ValueError(
                    f"Model format {model.data.basic.format} not in graphers dictionary."
                    f"Allowed formats: {list(self.graphers.keys())}"
                ) from e

        for solver in self.solvers:
            try:
                self.graphers[solver.get_solver_name()].add(solver)
            except KeyError as e:
                raise ValueError(
                    f"Model format {solver.get_solver_name()} not in graphers dictionary."
                    f"Allowed formats: {list(self.graphers.keys())}"
                ) from e

    def generate_graphs(self):
        """Generate and save all graphs."""
        graph_dir = self.output_path._path / "graphs"
        graph_dir.mkdir(exist_ok=True)
        for fmt, grapher in self.graphers.items():
            grapher.generate_all_figures()
            if grapher.figures:
                output_dir = graph_dir / (fmt + "_graphs")
                output_dir.mkdir(exist_ok=True)
                grapher.save_figures(output_dir)


class BaseGrapher(ABC):
    def __init__(self):
        self.logger = logging.getLogger(f"bt.{self.__class__.__name__.lower()}")
        self.figures = {}
        self._setup_style()
        self.worked = False

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

    @abstractmethod
    def generate_all_figures(self):
        """Generate all standard figures for this model type"""
        pass

    def save_figures(self, output_path):
        """Save all generated figures"""
        for fig_name, fig in self.figures.items():
            path = output_path / f"{fig_name}.png"
            fig.savefig(path, dpi=300, bbox_inches="tight")
            plt.close(fig)
            self.logger.info(f"Saved {fig_name} to {path}")

    def show(self):
        """Display the graph interactively"""
        self.generate_all_figures()
        plt.show()


class ModelGrapher(BaseGrapher):
    """Abstract base class providing:
    - Consistent styling (colors, fonts, grids)
    - Multi-figure generation pipeline
    - Standardized saving/display methods
    """

    def __init__(self):
        super().__init__()
        self.models = []

    @abstractmethod
    def generate_all_figures(self) -> dict[str, plt.Figure]:
        pass

    def add(self, model):
        self.models.append(model)


class SolverGrapher(BaseGrapher):
    def __init__(self):
        super().__init__()
        self.solver = None

    def generate_all_figures(self) -> dict[str, plt.Figure]:
        if not self.solver:
            return
        
        self.logger.info(f"Generating figures for {self.solver.get_solver_name()} solver")
        self.figures = {
            "cpu_usage_figure": self._create_cpu_usage_figure(),
            "memory_usage": self._create_memory_usage_figure(),
            "average_memory_usage": self._create_average_memory_usage_figure()
        }

        # Remove None values in case any figure failed
        self.figures = {k: v for k, v in self.figures.items() if v is not None}
    
    def _create_cpu_usage_figure(self) -> plt.Figure:
        """Line plot with automatic CPU range scaling and status coloring."""
        samples = self.solver.data.profile.samples
        
        if not samples:
            self.logger.debug("No CPU usage data available")
            return None

        fig, ax = plt.subplots(figsize=self.figsize)
        
        # Color configuration
        success_color = ColorMap.PRIMARY['green']
        failure_color = ColorMap.PRIMARY['red']
        
        # Track legend entries to avoid duplicates
        legend_handles = {
            'Solved': None,
            'Unsolved': None
        }

        # Collect all CPU values for scaling
        all_cpus = []
        plot_data = []

        for model, measurements in samples.items():
            if len(measurements) < 2:
                continue

            # Get solve status
            solved = model in self.solver.data.solved
            
            # Extract timeline relative to first measurement
            base_time = measurements[0].timestamp
            times = [m.timestamp - base_time for m in measurements]
            cpus = [m.cpu_percent for m in measurements]
            all_cpus.extend(cpus)
            
            plot_data.append((model, times, cpus, solved))

        # Calculate smart axis limits
        if all_cpus:
            cpu_min = max(0, min(all_cpus) - 5)  # Pad bottom by 5%
            cpu_max = min(120, max(all_cpus) + 5)  # Cap at 120% with padding
            if cpu_max < 50:  # Handle unusually low CPU cases
                cpu_max = 100
        else:
            cpu_min, cpu_max = 0, 100

        # Plot all models with calculated scaling
        for model, times, cpus, solved in plot_data:
            line = ax.plot(
                times,
                cpus,
                label=self._truncate_name(model.data.basic.name, 15),
                color=success_color if solved else failure_color,
                alpha=0.7,
                linewidth=1.5,
                marker='o' if len(times) < 20 else None,
                markersize=4
            )[0]
            
            # Store legend handles
            if solved and not legend_handles['Solved']:
                legend_handles['Solved'] = line
            elif not solved and not legend_handles['Unsolved']:
                legend_handles['Unsolved'] = line

        # Formatting with dynamic scaling
        self._format_axes(
            ax, fig,
            title="CPU Usage Timeline (Solved vs Unsolved Models)",
            xlabel="Time (seconds)",
            ylabel="CPU Utilization (%)",
            grid=True
        )
        
        # Set dynamic Y-axis limits
        ax.set_ylim(cpu_min, cpu_max)
        ax.axhline(100, color='#888888', linestyle=':', linewidth=0.5)  # 100% marker
        
        # Create combined legend
        final_handles = []
        if legend_handles['Solved']:
            final_handles.append(legend_handles['Solved'])
        if legend_handles['Unsolved']:
            final_handles.append(legend_handles['Unsolved'])
            
        ax.legend(
            final_handles,
            [h for h in legend_handles.keys() if legend_handles[h]],
            title="Model Status",
            bbox_to_anchor=(1.05, 1),
            loc='upper left',
            borderaxespad=0.
        )

        # Secondary legend for model names
        model_legend = ax.legend(
            title="Model Names",
            bbox_to_anchor=(1.05, 0),
            loc='lower left',
            borderaxespad=0.
        )
        ax.add_artist(model_legend)

        ax.set_xlim(left=0)
        ax.xaxis.set_major_locator(plt.MultipleLocator(10))
        
        # Add CPU range annotation if needed
        if cpu_max > 105:
            ax.text(0.98, 0.95, 
                f"CPU Range: {min(all_cpus):.0f}-{max(all_cpus):.0f}%",
                transform=ax.transAxes,
                ha='right', va='top',
                bbox=dict(facecolor='white', alpha=0.7))
        
        return fig
    
    def _create_memory_usage_figure(self) -> plt.Figure:
        """Line plot with automatic CPU range scaling and status coloring."""
        samples = self.solver.data.profile.samples
        
        if not samples:
            self.logger.debug("No memory usage data available")
            return None

        fig, ax = plt.subplots(figsize=self.figsize)
        
        # Color configuration
        success_color = ColorMap.PRIMARY['green']
        failure_color = ColorMap.PRIMARY['red']
        
        # Track legend entries to avoid duplicates
        legend_handles = {
            'Solved': None,
            'Unsolved': None
        }

        # Collect all CPU values for scaling
        all_memory_usage = []
        plot_data = []

        for model, measurements in samples.items():
            if len(measurements) < 2:
                continue

            # Get solve status
            solved = model in self.solver.data.solved
            
            # Extract timeline relative to first measurement
            base_time = measurements[0].timestamp
            times = [m.timestamp - base_time for m in measurements]
            memory_usage = [m.rss for m in measurements]
            all_memory_usage.extend(memory_usage)
            
            plot_data.append((model, times, memory_usage, solved))

        # Calculate smart axis limits
        if all_memory_usage:
            rss_min = min(all_memory_usage)
            rss_max = max(all_memory_usage) 

        # Plot all models with calculated scaling
        for model, times, cpus, solved in plot_data:
            line = ax.plot(
                times,
                cpus,
                label=self._truncate_name(model.data.basic.name, 15),
                color=success_color if solved else failure_color,
                alpha=0.7,
                linewidth=1.5,
                marker='o' if len(times) < 20 else None,
                markersize=4
            )[0]
            
            # Store legend handles
            if solved and not legend_handles['Solved']:
                legend_handles['Solved'] = line
            elif not solved and not legend_handles['Unsolved']:
                legend_handles['Unsolved'] = line

        # Formatting with dynamic scaling
        self._format_axes(
            ax, fig,
            title="RSS Timeline (Solved vs Unsolved Models)",
            xlabel="Time (seconds)",
            ylabel="RSS (MB)",
            grid=True
        )
        
        # Set dynamic Y-axis limits
        ax.set_ylim(rss_min, rss_max)
        ax.axhline(100, color='#888888', linestyle=':', linewidth=0.5)  # 100% marker
        
        # Create combined legend
        final_handles = []
        if legend_handles['Solved']:
            final_handles.append(legend_handles['Solved'])
        if legend_handles['Unsolved']:
            final_handles.append(legend_handles['Unsolved'])
            
        ax.legend(
            final_handles,
            [h for h in legend_handles.keys() if legend_handles[h]],
            title="Model Status",
            bbox_to_anchor=(1.05, 1),
            loc='upper left',
            borderaxespad=0.
        )

        # Secondary legend for model names
        model_legend = ax.legend(
            title="Model Names",
            bbox_to_anchor=(1.05, 0),
            loc='lower left',
            borderaxespad=0.
        )
        ax.add_artist(model_legend)

        ax.set_xlim(left=0)
        ax.xaxis.set_major_locator(plt.MultipleLocator(10))
        
        return fig

    def _create_average_memory_usage_figure(self) -> plt.Figure:
        """Creates memory usage plot with time in seconds (sample index × 10)."""
        if not self.solver.data.profile.samples:
            self.logger.debug("No memory usage data available")
            return None

        fig, ax = plt.subplots(figsize=self.figsize)
        
        # Configuration
        line_styles = {
            'Solved': {
                'color': ColorMap.PRIMARY['green'],
                'label': 'Solved models',
                'data': []
            },
            'Unsolved': {
                'color': ColorMap.PRIMARY['red'],
                'label': 'Unsolved models',
                'data': []
            }
        }

        # Group data by solve status
        for model, measurements in self.solver.data.profile.samples.items():
            if len(measurements) < 2:
                continue
                
            status = 'Solved' if model in self.solver.data.solved else 'Unsolved'
            line_styles[status]['data'].append([m.rss for m in measurements])

        # Plot average lines
        plotted_lines = []
        for status, style in line_styles.items():
            if not style['data']:
                continue
                
            # Calculate average at each time point
            max_len = max(len(m) for m in style['data'])
            avg_line = [
                np.mean([m[i] for m in style['data'] if i < len(m)])
                for i in range(max_len)
            ]
            
            # Convert sample index to seconds (×10)
            time_points = [i * 10 for i in range(len(avg_line))]
            
            line = ax.plot(
                time_points,  # Use seconds instead of sample index
                avg_line,
                color=style['color'],
                linewidth=2,
                label=f"{style['label']} (n={len(style['data'])})"
            )[0]
            plotted_lines.append(line)

        # Only proceed if we have data to plot
        if not plotted_lines:
            plt.close(fig)
            return None

        # Formatting
        self._format_axes(
            ax, fig,
            title=f"{self.solver.get_solver_name()} Memory Usage",
            xlabel="Time (seconds)",
            ylabel="RSS (MB)",
            grid=True
        )
        
        # Set Y-axis limits with buffer
        all_values = [y for line in plotted_lines for y in line.get_ydata()]
        y_min, y_max = min(all_values), max(all_values)
        buffer = 0.1 * (y_max - y_min)
        ax.set_ylim(y_min - buffer, y_max + buffer)

        # Add legend only if we have lines to show
        if plotted_lines:
            ax.legend(
                title="Color Coding:",
                bbox_to_anchor=(1.05, 1),
                loc='upper left',
                borderaxespad=0.,
                framealpha=1,
                edgecolor='black'
            )

        # Add reference line
        ax.axhline(100, color='#888888', linestyle=':', linewidth=0.5)
        
        plt.tight_layout()
        return fig

    def _truncate_name(self, name: str, max_length: int) -> str:
        """Helper to shorten long model names for legends"""
        return (name[:max_length] + '..') if len(name) > max_length else name

    
    def add(self, solver):
        self.solver = solver

class SMT2ModelGrapher(ModelGrapher):
    def __init__(self):
        super().__init__()


    def generate_all_figures(self) -> dict[str, plt.Figure]:
        """Generate standard battery of SMT2 analysis figures"""
        if not self.models:
            return
        
        self.logger.info(f"Creating figures for SMT2 models")
        self.figures = {
            "line_counts": self._create_line_count_figure(),
            "define_distribution": self._create_define_figure(),
            "metrics_per_line": self._create_avg_metrics_per_line_figure(),
            "check_sat_per_line_to_solve_time": self._create_check_sat_per_line_to_solve_time_figure(),
            "source_code_size_to_solve_time": self._create_source_code_size_to_solve_time_figure()
        }

        # Remove None values in case any figure failed
        self.figures = {k: v for k, v in self.figures.items() if v is not None}
    
    def _create_source_code_size_to_solve_time_figure(self) -> plt.Figure:
        """Scatter plot with model names annotated for outlier points."""
        # Filter valid models
        valid_models = [
            m for m in self.models 
            if (m.data.parsed.is_rotor_generated and  
                m.data.best_run and
                m.data.best_run.success )
        ]
        
        if not valid_models:
            self.logger.debug("No valid models for source code size analysis")
            return None

        # Prepare data with names
        data = []
        for model in valid_models:
            try:
                code_size = float(model.data.parsed.rotor_data.source_code_size)
                time = model.data.best_run.elapsed_time
                if code_size > 0 and time > 0:
                    data.append({
                        "code_size": code_size,
                        "time": time,
                        "solver": model.data.best_run.solver_used,
                        "name": model.data.basic.name
                    })
            except (TypeError, ValueError) as e:
                self.logger.debug(f"Invalid data in {model.data.basic.name}: {e}")
                continue

        if len(data) < 3:
            return None

        # Create figure
        fig, ax = plt.subplots(figsize=(12, 8))
        
        # Color by solver
        solver_colors = {
            d["solver"]: ColorMap.SOLVER[d["solver"].lower()]
            for d in data
        }
        
        # Plot points
        for solver, color in solver_colors.items():
            subset = [d for d in data if d["solver"] == solver]
            ax.scatter(
                x=[d["code_size"] for d in subset],
                y=[d["time"] for d in subset],
                c=color,
                s=40,
                edgecolor='white',
                label=solver.upper(),
                alpha=0.8
            )

        # Calculate median thresholds
        code_sizes = [d["code_size"] for d in data]
        times = [d["time"] for d in data]
        median_code_size = np.median(code_sizes)
        median_time = np.median(times)

        # Annotate interesting points
        for d in data:
            # Label if in top 25% of either dimension
            if d["code_size"] > np.percentile(code_sizes, 75) or d["time"] > np.percentile(times, 75):
                ax.annotate(
                    d["name"],
                    (d["code_size"], d["time"]),
                    textcoords="offset points",
                    xytext=(5, -5),  # Offset downward
                    ha='left',
                    va='top',
                    fontsize=8,
                    color=self.colors["text"],
                    arrowprops=dict(
                        arrowstyle="-",
                        color="#888888",
                        linewidth=0.5
                    )
                )

        # Formatting
        self._format_axes(
            ax, fig,
            title="Source Code Size vs Solve Time",
            xlabel="Source Code Size",
            ylabel="Solve Time [s]"
        )
        
        # Add legend and info box
        ax.legend(title="Solver", frameon=True)
        info_text = f"""Models: {len(data)}
        ▲ Upper right: Source Code Size > {median_code_size:.1e}
        ► Right half: Time > {median_time:.1f}s"""
        ax.text(
            0.95, 0.15,
            info_text,
            transform=ax.transAxes,
            ha='right',
            va='bottom',
            fontsize=9,
            bbox=dict(facecolor='white', alpha=0.8)
        )

        return fig

    
    def _create_check_sat_per_line_to_solve_time_figure(self):
        #Prepare data
        solved_models = [model for model in self.models if model.data.best_run and model.data.best_run.success]

        if not solved_models:
            self.logger.debug("No valid models for (check_sat) analysis")
            return None

        x, y, solvers = [], [], []
        for model in solved_models:
            x_val = model.data.parsed.check_sats_per_line()
            if x_val <= 0:  # Skip models with no check-sat
                continue
        
            x.append(x_val)
            y.append(model.data.best_run.elapsed_time)
            solvers.append(model.data.best_run.solver_used)
    
        # Create figure
        fig, ax = plt.subplots(figsize=self.figsize)
    
        # Color by solver using project colormap
        solver_colors = {
            solver: ColorMap.SOLVER[solver.lower()]
            for solver in set(solvers)
        }
        
        # Plot each point with solver-specific color
        for solver, color in solver_colors.items():
            mask = [s == solver for s in solvers]
            ax.scatter(
                x=np.array(x)[mask],
                y=np.array(y)[mask],
                c=color,
                s=80,
                edgecolor="white",
                label=solver.upper(),
                zorder=3
            )

        # Formatting
        ax.set_yscale('log')
        self._format_axes(
            ax, fig,
            title="Check-sat Density vs Solve Time",
            xlabel="Check-sat Commands per Line",
            ylabel="Solve Time (seconds, log scale)"
        )
        
        # Add legend and annotations
        ax.legend(title="Solver", frameon=True, framealpha=0.9)
        ax.annotate(
            f"n = {len(x)} models",
            xy=(0.95, 0.9), xycoords='axes fraction',
            ha='right', va='top',
            bbox=dict(boxstyle="round,pad=0.3", fc="white", ec="none")
        )

        # Highlight outliers
        if len(y) > 10:  # Only annotate if sufficient data
            q75, q25 = np.percentile(y, [75, 25])
            iqr = q75 - q25
            for xi, yi, name in zip(x, y, [m.data.basic.name for m in solved_models]):
                if yi > q75 + 1.5*iqr:
                    ax.annotate(
                        name, (xi, yi),
                        textcoords="offset points",
                        xytext=(0,5), ha='center',
                        fontsize=8, color=self.colors["highlight"]
                    )

        return fig
        


    def _create_line_count_figure(self):
        """Core graphing logic"""
        colors = {
            "bars": ColorMap.PRIMARY["blue"],
            "avg_line": ColorMap.PRIMARY["red"],
            "text": "#333333",
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
        #Add legend
        ax.legend()

        # Value labels
        if len(names) < 20:
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
        
        if len(names) > 20:
            ax.set_xticks([])
            ax.set_xticklabels([])

        self._format_axes(ax, fig, "Model Line Counts", "Models", "Total Lines")
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

    def generate_all_figures(self):
        """Core graphing logic"""
        if not self.models:
            return

        self.logger.info(f"Creating figures for BTOR2 models")
        self.figures = {}
