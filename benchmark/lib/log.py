import logging
from pathlib import Path
from typing import Union

def get_log_level(verbosity: int) -> str:
    """Map numeric verbosity (0-4) to logging levels"""
    return {
        0: 'CRITICAL',  # Only show critical errors
        1: 'ERROR',     # Show errors
        2: 'WARNING',   # Show warnings
        3: 'INFO',      # Basic info (default)
        4: 'DEBUG'      # Detailed debugging
    }.get(verbosity, 'INFO')  # Default to INFO if invalid

def configure_logging(
    verbosity: int = 4,          # 0-4 scale (default: 3=INFO)
    log_dir: Union[Path, str] = None,
):
    """Initialize logging with verbosity levels"""
    
    console_level = get_log_level(verbosity)
    file_level = get_log_level(verbosity)
    
    root_logger = logging.getLogger("bt")
    root_logger.setLevel(logging.DEBUG)  # Lowest level, handlers filter
    
    # Clean up existing handlers to avoid duplicates
    for handler in root_logger.handlers[:]:
        root_logger.removeHandler(handler)
    
    # Console handler with simplified format
    console_handler = logging.StreamHandler()
    console_handler.setLevel(console_level)
    console_handler.setFormatter(logging.Formatter(
        '%(asctime)s %(levelname)-8s %(message)s',
        datefmt='%H:%M'
    ))
    root_logger.addHandler(console_handler)
    
    # File handler (if enabled)
    if log_dir:
        log_dir = Path(log_dir)
        log_dir.mkdir(exist_ok=True)
        
        file_handler = logging.FileHandler(log_dir / "bt_debug.log")
        file_handler.setLevel(file_level)
        file_handler.setFormatter(logging.Formatter(
            '%(asctime)s %(name)s %(levelname)s %(message)s'
        ))
        root_logger.addHandler(file_handler)