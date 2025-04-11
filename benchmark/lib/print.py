import sys
import logging

logger = logging.getLogger("bt.exit")

def custom_exit(message, code=0):
    logger.log(message)
    sys.exit(code)
