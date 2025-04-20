import time

from bitwuzla import *

class TimeTerminator:

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