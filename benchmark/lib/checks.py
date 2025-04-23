from .exceptions import (
    TimeoutException,
)
import lib.config as cfg

from subprocess import Popen, TimeoutExpired
import shlex
import sys
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
    process = Popen(shlex.split(command), stdout=cfg.PIPE, stderr=cfg.STDOUT, cwd=cwd)

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
