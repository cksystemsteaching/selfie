import logging
from pathlib import Path

def configure_logging(log_dir: Path = None, console_level: str = "INFO", file_level: str = "DEBUG"):
    """ Initialize hierarchical logging system """

    # Create a root logger
    root_logger = logging.getLogger("bt")
    root_logger.setLevel(logging.DEBUG)

    # Standard formatter
    formatter = logging.Formatter(
        '%(asctime)s - %(name)s - %(levelname)s - %(message)s', "%H:%M")
    
    # Console handler (all components)
    console_handler = logging.StreamHandler()
    console_handler.setLevel(console_level)
    console_handler.setFormatter(formatter)
    root_logger.addHandler(console_handler)
    
    # File handler if specified
    if log_dir:
        log_dir.mkdir(exist_ok=True)
        file_handler = logging.FileHandler(log_dir / "project.log")
        file_handler.setLevel(file_level)
        file_handler.setFormatter(formatter)
        root_logger.addHandler(file_handler)