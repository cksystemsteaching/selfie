from .exceptions import (
    TimeoutException,
)
import lib.config as cfg

from subprocess import Popen, TimeoutExpired
import shlex
import sys


def is_tool_available(name) -> bool:
    from shutil import which
    return which(name) is not None

def execute(command, timeout=200):
    process = Popen(shlex.split(command), stdout=cfg.PIPE, stderr=cfg.STDOUT)

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
