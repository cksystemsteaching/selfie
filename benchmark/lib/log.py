"""
Custom logging setup for BT with:
- Verbose info level (between DEBUG and INFO)
- Separate loggers for CLI and file output
- Clean handler management to prevent duplicates

Usage:
    configure_logging(verbosity=True, log_file="debug.log")
    logger = logging.getLogger("bt-cli")
    logger.verbose_info("Detailed diagnostic message")
"""

from pathlib import Path
from typing import Union
import logging


VERBOSE_INFO_LEVEL = 19  # Lower than INFO (20)

# Register the levels
logging.addLevelName(VERBOSE_INFO_LEVEL, "VERBOSE_INFO")


def verbose_info(self, message, *args, **kwargs):
    if self.isEnabledFor(VERBOSE_INFO_LEVEL):
        self._log(VERBOSE_INFO_LEVEL, message, args, **kwargs)


logging.Logger.verbose_info = verbose_info


def get_log_level(verbose: bool) -> int:
    """Returns the threshold level for filtering logs."""
    return "VERBOSE_INFO" if verbose else "INFO"


def configure_logging(
    verbosity: bool = False,
    log_file: Union[Path, str] = None,
):
    """Initialize logging with verbosity levels"""

    console_level = get_log_level(verbosity)
    file_level = get_log_level(verbosity)

    root_logger = logging.getLogger("bt")
    root_logger.setLevel(logging.DEBUG)

    cli_logger = logging.getLogger("bt-cli")
    cli_logger.setLevel(logging.DEBUG)

    file_logger = logging.getLogger("bt-file")
    file_logger.setLevel(logging.DEBUG)

    # Clean up existing handlers to avoid duplicates
    for handler in root_logger.handlers[:]:
        root_logger.removeHandler(handler)

    for handler in cli_logger.handlers[:]:
        cli_logger.removeHandler(handler)

    for handler in file_logger.handlers[:]:
        file_logger.removeHandler(handler)

    # Console handler with simplified format
    console_handler = logging.StreamHandler()
    console_handler.setLevel(console_level)
    console_handler.setFormatter(
        logging.Formatter("%(asctime)s %(levelname)-8s %(message)s", datefmt="%H:%M")
    )
    root_logger.addHandler(console_handler)
    cli_logger.addHandler(console_handler)

    # File handler (if enabled)
    if log_file:
        file_handler = logging.FileHandler(log_file)
        file_handler.setLevel(file_level)
        file_handler.setFormatter(
            logging.Formatter("%(asctime)s %(name)s %(levelname)s %(message)s")
        )
        root_logger.addHandler(file_handler)
        file_logger.addHandler(file_handler)
