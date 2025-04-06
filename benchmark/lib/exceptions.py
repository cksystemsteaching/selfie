from .config import RED, RESET
import logging

import logging
from pathlib import Path

import logging
from pathlib import Path

import logging
from pathlib import Path

class BTError(Exception):
    """Base class for all SMT tool exceptions"""
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
            #exc_info=True  # This preserves the traceback
        )

class FileValidationError(BTError):
    """Automatically logs file validation errors"""
    def __init__(self, message: str, path: Path, **kwargs):
        super().__init__(
            message,
            {
                'path': str(path),
                'resolved_path': str(path.resolve()),
                **kwargs
            }
        )

class ToolNotAvailableError(Exception):
    def __init__(self, tool):
        Exception.__init__(self, f"{RED}Error: {RESET} {tool} is not available on this machine.")


class DirectoryNotFoundError(Exception):
    def __init__(self, dir):
        Exception.__init__(self, f"{RED}Error: {RESET} {dir} directory does not exist.")


class InternalToolNotAvailableError(Exception):
    def __init__(self, tool):
        Exception.__init__(self, f"{RED}Error: {RESET} {tool} is not available inside project's directory.")


class TimeoutException(Exception):
    def __init__(self, command, timeout, output): # , error_output:
        Exception.__init__(self, 'The command \"' + command +
                           '\" has timed out after ' + str(timeout) + 's')
        self.output = output
        # self.error_output = error_output


class ParsingError(Exception):
    def __init__(self, parsed_string, error_part):
        Exception.__init__(self, f"{RED}Error: {RESET} Parsing error has occured in {parsed_string}, specifically in {error_part}.")
