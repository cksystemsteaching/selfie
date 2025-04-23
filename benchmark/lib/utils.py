import os
import sys
import contextlib


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
