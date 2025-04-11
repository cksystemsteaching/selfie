import logging
from pathlib import Path
from typing import Union

# Custom levels (between WARNING and INFO in severity)
VERBOSE_INFO_LEVEL = 19  # Higher than INFO (20), lower than WARNING (30)

# Register the levels
logging.addLevelName(VERBOSE_INFO_LEVEL, "VERBOSE_INFO")

# Optional: Add convenience methods to the logger
def verbose_info(self, message, *args, **kwargs):
    if self.isEnabledFor(VERBOSE_INFO_LEVEL):
        self._log(VERBOSE_INFO_LEVEL, message, args, **kwargs)

logging.Logger.verbose_info = verbose_info

def get_log_level(verbose: bool) -> int:
    """Returns the threshold level for filtering logs."""
    return 'VERBOSE_INFO' if verbose else 'INFO'

def configure_logging(
    verbosity: int = 4,          # 0-4 scale (default: 3=INFO)
    log_file: Union[Path, str] = None,
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
    if log_file:        
        file_handler = logging.FileHandler(log_file)
        file_handler.setLevel(file_level)
        file_handler.setFormatter(logging.Formatter(
            '%(asctime)s %(name)s %(levelname)s %(message)s'
        ))
        root_logger.addHandler(file_handler)