from enum import Enum


# BEGIN 0-BIT
def get_MATRIARCH0_config():
    configurations = {
        #    x1  x2   z
        (0, 0, 0),  # F F | T
        (0, 1, 0),  # F T | F
        (1, 0, 0),  # T F | F
        (1, 1, 0)  # T T | F
    }
    return configurations


# END 0-BIT
# BEGIN 1-BIT
def get_NOR_config():
    configurations = {
        #    x1  x2   z
        (0, 0, 1),  # F F | T
        (0, 1, 0),  # F T | F
        (1, 0, 0),  # T F | F
        (1, 1, 0)  # T T | F
    }
    return configurations


def get_MATRIARCH1_config():
    configurations = {
        #    x1  x2   z
        (0, 0, 0),  # F F | F
        (0, 1, 1),  # F T | T
        (1, 0, 0),  # T F | F
        (1, 1, 0)  # T T | F
    }
    return configurations


def get_MATRIARCH2_config():
    configurations = {
        #    x1  x2   z
        (0, 0, 0),  # F F | F
        (0, 1, 0),  # F T | F
        (1, 0, 1),  # T F | T
        (1, 1, 0)  # T T | F
    }
    return configurations


def get_AND_config():
    configurations = {
        #    x1  x2   z
        (0, 0, 0),  # F F | F
        (0, 1, 0),  # F T | F
        (1, 0, 0),  # T F | F
        (1, 1, 1)  # T T | T
    }
    return configurations


# END 1-BIT
# BEGIN 2-BIT
def get_MATRIARCH3_config():
    configurations = {
        #    x1  x2   z
        (0, 0, 1),  # F F | T
        (0, 1, 1),  # F T | T
        (1, 0, 0),  # T F | F
        (1, 1, 0)  # T T | F 
    }
    return configurations


def get_MATRIARCH4_config():
    configurations = {
        #    x1  x2   z
        (0, 0, 1),  # F F | T
        (0, 1, 0),  # F T | F
        (1, 0, 1),  # T F | T
        (1, 1, 0)  # T T | F 
    }
    return configurations


def get_XNOR_config():
    configurations = {
        #    x1  x2   z
        (0, 0, 1),  # F F | T
        (0, 1, 0),  # F T | F
        (1, 0, 0),  # T F | F
        (1, 1, 1)  # T T | T 
    }
    return configurations


def get_XOR_config():
    configurations = {
        #    x1 x2 z
        (0, 0, 0),  # F F | F
        (0, 1, 1),  # F T | T
        (1, 0, 1),  # T F | T
        (1, 1, 0)  # T T | F 
    }
    return configurations


def get_MATRIARCH5_config():
    configurations = {
        #    x1  x2   z
        (0, 0, 0),  # F F | F
        (0, 1, 1),  # F T | T
        (1, 0, 0),  # T F | F
        (1, 1, 1)  # T T | T 
    }
    return configurations


def get_MATRIARCH6_config():
    configurations = {
        #    x1  x2   z
        (0, 0, 0),  # F F | F
        (0, 1, 0),  # F T | F
        (1, 0, 1),  # T F | T
        (1, 1, 1)  # T T | T 
    }
    return configurations


# END 2-BIT
# BEGIN 3-BIT

def get_NAND_config():
    configurations = {
        #    x1  x2   z
        (0, 0, 1),  # F F | T
        (0, 1, 1),  # F T | T
        (1, 0, 1),  # T F | T
        (1, 1, 0)  # T T | F
    }
    return configurations


def get_MATRIARCH7_config():
    configurations = {
        #    x1  x2   z
        (0, 0, 1),  # F F | T
        (0, 1, 1),  # F T | T
        (1, 0, 0),  # T F | F
        (1, 1, 1)  # T T | T
    }
    return configurations


def get_MATRIARCH8_config():
    configurations = {
        #    x1  x2   z
        (0, 0, 1),  # F F | T
        (0, 1, 0),  # F T | F
        (1, 0, 1),  # T F | T
        (1, 1, 1)  # T T | T
    }
    return configurations


def get_OR_config():
    configurations = {
        #    x1  x2   z
        (0, 0, 0),  # F F | F
        (0, 1, 1),  # F T | T
        (1, 0, 1),  # T F | T
        (1, 1, 1)  # T T | T
    }
    return configurations


# BEGIN 4-bit
def get_MATRIARCH9_config():
    configurations = {
        #    x1  x2   z
        (0, 0, 1),  # F F | T
        (0, 1, 1),  # F T | T
        (1, 0, 1),  # T F | T
        (1, 1, 1)  # T T | T
    }
    return configurations


# END 4-bit

def get_NOT_config():
    configurations = {
        (0, 1),
        (1, 0)
    }
    return configurations


class Config(Enum):
    MATRIARCH0 = 0
    NOR = 1
    MATRIARCH1 = 2
    MATRIARCH2 = 3
    AND = 4
    MATRIARCH3 = 5
    MATRIARCH4 = 6
    XNOR = 7
    XOR = 8
    MATRIARCH5 = 9
    MATRIARCH6 = 10
    NAND = 11
    MATRIARCH7 = 12
    MATRIARCH8 = 13
    OR = 14
    MATRIARCH9 = 15
    NOT = 16


def get_config(config):
    if Config.MATRIARCH0 == config:
        return get_MATRIARCH0_config(), "MATRIARCH0"

    elif Config.NOR == config:
        return get_NOR_config(), "NOR"

    elif Config.MATRIARCH1 == config:
        return get_MATRIARCH1_config(), "MATRIARCH1"

    elif Config.MATRIARCH2 == config:
        return get_MATRIARCH2_config(), "MATRIARCH2"

    elif Config.AND == config:
        return get_AND_config(), "AND"

    elif Config.MATRIARCH3 == config:
        return get_MATRIARCH3_config(), "MATRIARCH3"

    elif Config.MATRIARCH4 == config:
        return get_MATRIARCH4_config(), "MATRIARCH4"

    elif Config.XNOR == config:
        return get_XNOR_config(), "XNOR"

    elif Config.XOR == config:
        return get_XOR_config(), "XOR"

    elif Config.MATRIARCH5 == config:
        return get_MATRIARCH5_config(), "MATRIARCH5"

    elif Config.MATRIARCH6 == config:
        return get_MATRIARCH6_config(), "MATRIARCH6"

    elif Config.NAND == config:
        return get_NAND_config(), "NAND"

    elif Config.MATRIARCH7 == config:
        return get_MATRIARCH7_config(), "MATRIARCH7"

    elif Config.MATRIARCH8 == config:
        return get_MATRIARCH8_config(), "MATRIARCH8"

    elif Config.OR == config:
        return get_OR_config(), "OR"

    elif Config.MATRIARCH9 == config:
        return get_MATRIARCH9_config(), "MATRIARCH9"

    elif Config.NOT == config:
        return get_NOT_config(), "NOT"

    else:
        raise Exception("Not a valid configuration")
