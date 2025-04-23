import time

from bitwuzla import *


class TimeTerminator:
    """Callback handler for enforcing time limits in Bitwzla solver operations.

    This class implements a termination callback that can be used to enforce
    time limits when solving SMT problems with the Bitwzla library. The callback
    will signal termination when the specified time limit has been exceeded

    More here: https://bitwuzla.github.io/docs/cpp/classes/terminator.html
    """

    def __init__(self, time_limit):
        self.start_time = time.time()
        self.time_limit = time_limit
        self.activated = False

    def __call__(self):
        # Terminate after self.time_limit ms passed
        should_terminate = (time.time() - self.start_time) > self.time_limit
        if should_terminate:
            self.activated = True
        return should_terminate
