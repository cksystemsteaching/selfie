import lib.constants as const

from subprocess import Popen
import shlex
import sys

class ToolNotAvailableError(Exception):
    pass

class TimeoutException(Exception):
    def __init__(self, command, timeout, output): # , error_output:
        Exception.__init__(self, 'The command \"' + command +
                           '\" has timed out after ' + str(timeout) + 's')
        self.output = output
        # self.error_output = error_output


def is_tool_available(name) -> bool:
    from shutil import which
    return which(name) is not None


def check_needed_tools() -> None:
    check_internal_tools(const.rotor_path)
    check_directory(const.examples_dir)
    # check_tool("riscv64-unknown-elf-gcc")


def check_tool(name) -> None:
    print(f"Checking if {name} is available...")
    if not is_tool_available(name):
        raise ToolNotAvailableError(f"Error: {name} is not available on this machine")


def check_internal_tools(tool) -> None:
    print(f"Checking if {tool} is exists...")
    if not tool.is_file():
        raise ToolNotAvailableError(f"Error: {tool} is not available inside project's directory")


def check_directory(dir) -> None:
    print(f"Checking if {dir} exists...")
    if not dir.is_dir():
        raise ToolNotAvailableError(f"Error: {dir} directory doesn't exist...")


def execute(command, timeout=30):
    process = Popen(shlex.split(command), stdout=const.PIPE, stderr=const.STDOUT)

    timedout = False

    if sys.version_info < (3, 3):
        stdoutdata, _ = process.communicate()
    else:
        try:
            stdoutdata, _ = process.communicate(timeout=timeout)
        except const.TimeoutExpired:
            process.kill()
            stout, _ = process.communicate()
            timedout = True
    output = stdoutdata.decode(sys.stdout.encoding)

    if timedout:
        raise TimeoutException(command, timeout, output)

    return (process.returncode, output)
