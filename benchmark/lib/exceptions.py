"""
Custom exception hierarchy for BT with automatic logging and rich context.

All exceptions:
1. Automatically log with context (via BTError._auto_log)
2. Preserve structured problem details (in .context)
3. Inherit from BTError for consistent error handling

Example:
    raise FileValidationError("Invalid SMT format", path=model_file)
"""

import lib.config as cfg

from pathlib import Path
import logging


class BTError(Exception):
    """Root exception that all BT errors inherit from.

    Args:
        message: Human-readable error description
        context: Additional debugging details (automatically logged)
    """

    def __init__(self, message: str, context: dict = None):
        super().__init__(message)
        self.context = context or {}
        self._auto_log()

    def _auto_log(self):
        """Automatically log the error with context"""
        logger = logging.getLogger("bt.error")
        # Include both message and context in the log
        logger.error(
            "%s - Context: %s",
            str(self),
            self.context,
            # exc_info=True  # This preserves the traceback
        )


class BTValueError(BTError):
    """Generic value erorr"""

    def __init__(self, message: str, value, **kwargs):
        super().__init__(
            message,
            {
                "value": value,
                **kwargs,
            },
        )


class FileValidationError(BTError):
    def __init__(self, message: str, path: Path, **kwargs):
        super().__init__(
            message, {"path": str(path), "resolved_path": str(path.resolve()), **kwargs}
        )


class ParsingError(BTError):
    def __init__(
        self, parsing_place: str, parsed_string: str, error_part: str, **kwargs
    ):
        message = f"While parsing {parsing_place} a parsing error has occured in '{parsed_string}'"
        if error_part and error_part != parsed_string:
            message + f", in the part '{error_part}'."
        super().__init__(
            message,
            {"parsed_string": parsed_string, "error_path": error_part, **kwargs},
        )


class UnreachableError(BTError):
    def __init__(self, error_option, valid_options, **kwargs):
        super().__init__(
            f"Invalid option provided. Received option: {error_option} and valid options were {valid_options}.",
            {"error_option": error_option, "valid_options": valid_options, **kwargs},
        )


class ConfigFormatError(BTError):
    def __init__(self, message, error_format, **kwargs):
        super().__init__(
            message,
            {
                "error_format": error_format,
                "config_formats": cfg.config["allowed_formats"],
                **kwargs,
            },
        )


class TimeoutException(BTError):
    def __init__(self, command, timeout, output):  # , error_output:
        super().__init__(
            f"The command {command} has timed out after {str(timeout)} s.",
            {"command": command, "timeout": timeout, "output": output},
        )
        self.output = output


class UnsupportedModelException(BTError):
    def __init__(self, message, model, **kwargs):
        super().__init__(message, {"model": model.data.basic.output_path, **kwargs})
