import os
import sys
import contextlib

@contextlib.contextmanager
def suppress_stdout():
    # Save the original stdout file descriptor (1)
    original_stdout_fd = sys.stdout.fileno()
    saved_stdout_fd = os.dup(original_stdout_fd)

    # Redirect stdout to null device
    with open(os.devnull, 'w') as devnull:
        os.dup2(devnull.fileno(), original_stdout_fd)
        try:
            yield
        finally:
            # Restore original stdout
            os.dup2(saved_stdout_fd, original_stdout_fd)
            os.close(saved_stdout_fd)