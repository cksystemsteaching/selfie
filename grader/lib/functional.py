import itertools

def flatmap(f, iterable):
    return itertools.chain.from_iterable(map(f, iterable))
