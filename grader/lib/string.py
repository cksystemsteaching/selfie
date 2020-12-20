def nfind(text: str, pattern: str, n: int):
    """
    Finds the n-th occurrence of a pattern in a string.
    This is done by calling str.find n times and passing the
    previously found index + 1 as start.
    """

    pos = -1
    for i in range(n):
        pos = text.find(pattern, pos + 1)
        if pos == -1:
            return -1

    return pos


def nrfind(text: str, pattern: str, n: int):
    """
    Finds the n-th occurrence of a pattern in a string in reverse.
    This is done by calling str.rfind n times and passing the
    previously found index - 1 as end.
    """

    pos = len(text) + 1
    for i in range(n):
        pos = text.rfind(pattern, 0, pos - 1)
        if pos == -1:
            return -1

    return pos
