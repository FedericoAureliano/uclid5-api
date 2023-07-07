"""
Python interface to UCLID5
"""

import z3


def IntegerSort():
    """
    Return the integer sort
    """
    return z3.IntSort()
