import z3


def integer():
    """
    Return the integer sort
    """
    return z3.IntSort()


def boolean():
    """
    Return the integer sort
    """
    return z3.BoolSort()


def real():
    """
    Return the real sort
    """
    return z3.RealSort()


def array(index, elem):
    """
    Return the array sort
    """
    return z3.ArraySort(index, elem)


def bitvector(size):
    """
    Return the bitvector sort
    """
    return z3.BitVecSort(size)
