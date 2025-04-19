import lib.config as cfg

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
class BTValueError(BTError):
    """Generic value erorr"""
    def __init__(self, message: str, value, **kwargs):
        super().__init__(
            message,
            {
                'value': value,
                **kwargs,
            }
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
class ParsingError(BTError):
    def __init__(self, parsed_string : str, error_part : str, **kwargs):
        super().__init__(
            f"Parsing error has occured in {parsed_string}, in the part {error_part}.",
            {
                'parsed_string': parsed_string,
                'error_path': error_part,
                **kwargs
            }
        )

class UnreachableError(BTError):
    def __init__(self, error_option, valid_options, **kwargs):
        super().__init__(
            f"Invalid option provided. Received option: {error_option} and valid options were {valid_options}.",
            {
                'error_option': error_option,
                'valid_options': valid_options,
                **kwargs
            }
        )

class ConfigFormatError(BTError):
    def __init__(self,message, error_format, **kwargs):
        super().__init__(
            message,
            {
                'error_format': error_format,
                'config_formats': cfg.config['allowed_formats'],
                **kwargs
            }
        )

class TimeoutException(BTError):
    def __init__(self, command, timeout, output): # , error_output:
        super().__init__(
            f"The command {command} has timed out after {str(timeout)} s.",
            {
                'command' : command,
                'timeout' : timeout,
                'output': output
            }            
        )
        self.output = output

class UnsupportedModelException(BTError):
    def __init__(self, message, model, **kwargs):
        super().__init__(
            message,
            {
                'model': model,
                **kwargs
            }
        )