from .config import RED, RESET


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
