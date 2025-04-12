import lib.config as cfg
from lib.exceptions import ConfigFormatError
import logging
from abc import ABC, abstractmethod

import matplotlib.pyplot as plt
import numpy as np

class GrapherWrapper:
    def __init__(self, output_path, models):
        self.output_path = output_path if output_path.is_dir() else output_path.parent()
        self.models = models  # Store models as instance variable
        self.graphers = self._initialize_graphers()  # Initialize and validate
        self._distribute_models()
    
    def _initialize_graphers(self):
        """Initialize and validate format-specific graphers."""
        graphers = {
            'smt2': SMT2ModelGrapher(),
            'btor2': BTOR2ModelGrapher()
        }
        
        # Validate all required formats exist
        for fmt in cfg.config['allowed_formats']:
            if fmt not in graphers:
                raise ConfigFormatError(
                    message=f"Format '{fmt}' is not implemented",
                    error_format=fmt,
                    provided_formats=list(graphers.keys()),
                    class_name=self.__class__.__name__,
                    method="_initialize_graphers"
                )
        return graphers
    
    def _distribute_models(self):
        """Distribute models to their respective graphers."""
        for model in self.models:
            try:
                self.graphers[model.get_format()].add(model)
            except KeyError as e:
                raise ValueError(
                    f"Model format {model.get_format()} not in "
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
    """Abstract base class for model graphers with multi-figure support"""
    def __init__(self):
        self.models = []
        self.logger = logging.getLogger(f"bt.{self.__class__.__name__.lower()}")
        self._setup_style()
    
    def _setup_style(self):
        """Shared style configuration for all figures"""
        plt.style.use('seaborn-v0_8-whitegrid')
        self.colors = {
            'primary': '#4C72B0',
            'secondary': '#55A868',
            'highlight': '#E24A33',
            'text': '#555555',
            'bars': '#555555',
            'avg_line': '#FFFFFF'
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
            fig.savefig(path, dpi=300, bbox_inches='tight')
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
            "define_distribution": self._create_define_figure()
        }

    def _create_line_count_figure(self):
        """Core graphing logic"""
        # Prepare data
        names = [m.output_path.stem for m in self.models]
        line_counts = [m.parser.stats['total_lines'] for m in self.models]
        avg_lines = np.mean(line_counts)

        # Create figure
        fig, ax = plt.subplots(figsize=(10, 6))

        # Bar plot
        bars = ax.bar(names, line_counts, 
                     color=self.colors['bars'],
                     width=0.7,
                     edgecolor='white')

        # Average line
        ax.axhline(avg_lines, color=self.colors['avg_line'], 
                  linestyle='--', linewidth=2,
                  label=f'Average ({avg_lines:.1f} lines)')

        # Value labels
        for bar in bars:
            height = bar.get_height()
            ax.text(bar.get_x() + bar.get_width()/2., height,
                   f'{height}',
                   ha='center', va='bottom',
                   color=self.colors['text'])
         # Rotate long names
        if max(len(name) for name in names) > 8:
            plt.xticks(rotation=45, ha='right')
       
        self._format_axes(ax, fig, "Model Line Counts", "Model Name", "Total Lines")
        return fig
    
    def _create_define_figure(self) -> plt.Figure:
        """Figure 3: Define command distribution"""
        fig, ax = plt.subplots(figsize=self.figsize)
        
        defines = [m.parser.stats['define_count'] for m in self.models]
        ax.scatter([m.parser.stats['code_lines'] for m in self.models], defines,
                  color=self.colors['secondary'], s=100)
        
        # Formatting
        self._format_axes(ax, fig, "Define Commands vs Code Size", 
                         "Code Lines", "Define Commands")
        return fig

    def _format_axes(self, ax, fig, title, xlabel, ylabel):
        """Shared formatting helper"""
        ax.set_title(title, pad=15)
        ax.set_xlabel(xlabel, labelpad=10)
        ax.set_ylabel(ylabel, labelpad=10)
        if len(ax.get_xticklabels()) > 5:
            plt.setp(ax.get_xticklabels(), rotation=45, ha='right')
        fig.tight_layout()

class BTOR2ModelGrapher(ModelGrapher):
    def __init__(self):
        super().__init__()

    def show(self):
        pass

    def generate_all_figures(self):
        """Core graphing logic"""
        return {}
        