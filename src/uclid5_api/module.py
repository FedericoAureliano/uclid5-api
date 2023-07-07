"""
Python interface to UCLID5
"""

import z3

from .statements import ConcurentBlock, Invariant, SequentialBlock
from .utils import indent


class Module:
    """
    A UCLID5 module
    """

    def __init__(self, name):
        """
        Create a UCLID5 module
        """
        self.name = name
        self.init = SequentialBlock()
        self.next = ConcurentBlock()
        self.vars = []
        self.invs = []

    def declare_var(self, name, sort):
        """
        Add a variable to the module
        """
        v = z3.Const(name, sort)
        self.vars.append(v)
        return v

    def assert_invariant(self, name, inv):
        """
        Add an invariant to the module
        """
        self.invs.append(Invariant(name, inv))

    def __str__(self) -> str:
        """
        Return the string representation of the module
        """
        vars = indent("\n".join([f"var {v}: {v.sort()};" for v in self.vars]))
        init = indent("init " + str(self.init))
        next = indent("next " + str(self.next))
        invs = indent("\n".join([str(i) for i in self.invs]))
        out = f"module {self.name} {{\n{vars}\n{init}\n{next}\n{invs}\n}}"
        return out
