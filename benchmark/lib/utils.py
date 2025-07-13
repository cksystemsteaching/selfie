from .exceptions import (
    TimeoutException,
)
import lib.config as cfg

from subprocess import Popen, TimeoutExpired, PIPE, STDOUT
import shlex
import sys
import os
import contextlib
import logging


def is_tool_available(name) -> bool:
    from shutil import which

    return which(name) is not None


def check_model_builder() -> bool:
    mb_file = cfg.model_builder_path
    # Check if model builder binary exists
    if not mb_file.exists():
        logger = logging.getLogger("bt.check_model_builder")
        logger.warning(f"{mb_file} is not built. Attempting to build it.")
        returncode, output = execute(
            cfg.config["build_model_builder"], 20, mb_file.parent
        )
        if returncode != 0:
            logger.error(
                f"Not able to build the model builder. Command failed with following output: {output}"
            )
            raise RuntimeError()
        else:
            logger.info(f"{mb_file} sucessfully built. Continuing...")


def execute(command, timeout=200, cwd="."):
    process = Popen(shlex.split(command), stdout=PIPE, stderr=STDOUT, cwd=cwd)

    timedout = False

    if sys.version_info < (3, 3):
        stdoutdata, _ = process.communicate()
    else:
        try:
            stdoutdata, _ = process.communicate(timeout=timeout)
        except TimeoutExpired:
            process.kill()
            stdoutdata, _ = process.communicate()
            timedout = True
    output = stdoutdata.decode(sys.stdout.encoding)

    if timedout:
        raise TimeoutException(command, timeout, output)

    return (process.returncode, output)


@contextlib.contextmanager
def suppress_stdout():
    """Context manager for temporarily suppressing stdout output.

    Redirects stdout to the null device for the duration of the context block,
    then restores the original stdout. Useful for silencing third-party library functions
    while still allowing exceptions to propagate.

    Example:
        >>> with suppress_stdout():
        ...     print("This won't be visible")
        >>> print("This will be visible")
    """
    # Save the original stdout file descriptor (1)
    original_stdout_fd = sys.stdout.fileno()
    saved_stdout_fd = os.dup(original_stdout_fd)

    # Redirect stdout to null device
    with open(os.devnull, "w") as devnull:
        os.dup2(devnull.fileno(), original_stdout_fd)
        try:
            yield
        finally:
            # Restore original stdout
            os.dup2(saved_stdout_fd, original_stdout_fd)
            os.close(saved_stdout_fd)
