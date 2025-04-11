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
            #grapher.show()
            if grapher.models:
                grapher.save((self.output_path._path / fmt).with_suffix(".png"))

class ModelGrapher(ABC):
    """Abstract base class from model graphers"""
    def __init__(self):
        self.models = []
        self.logger = logging.getLogger(f"bt.{self.__class__.__name__.lower()}")
        self._setup_style()
    
    def _setup_style(self):
        """Configure matplotlib style"""
        plt.style.use('seaborn-v0_8-whitegrid')
        self.colors = {
            'bars': '#4C72B0',
            'avg_line': '#E24A33',
            'text': '#555555'
        }

    @abstractmethod
    def show(self):
        pass

    @abstractmethod
    def _create_figure(self):
        pass
    
    def save(self, path):
        """Save the graph to file"""
        self._create_figure()
        plt.savefig(path, dpi=300, bbox_inches='tight')
        plt.close()
        self.logger.info(f"Saved graph to {path}")
    
    def add(self, model):
        self.models.append(model)

class SMT2ModelGrapher(ModelGrapher):
    def __init__(self):
        super().__init__()
    
    def show(self):
        """Display the graph interactively"""
        self._create_figure()
        plt.show()

    def _create_figure(self):
        """Core graphing logic"""
        if not self.models:
            raise ValueError("No models to graph.")

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

        # Formatting
        ax.set_title('Model Line Count Analysis', pad=20)
        ax.set_xlabel('Model Name', labelpad=10)
        ax.set_ylabel('Total Lines', labelpad=10)
        ax.legend(frameon=True)

        # Rotate long names
        if max(len(name) for name in names) > 8:
            plt.xticks(rotation=45, ha='right')

        # Adjust layout
        plt.tight_layout()

class BTOR2ModelGrapher(ModelGrapher):
    def __init__(self):
        super().__init__()

    def show(self):
        pass

    def _create_figure(self):
        """Core graphing logic"""
        if not self.models:
            return
        pass
        