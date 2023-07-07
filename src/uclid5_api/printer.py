import z3
from z3.z3printer import Formatter


class UCLIDFormatter(Formatter):
    def __init__(self):
        Formatter.__init__(self)

    def pp_sort(self, s):
        if isinstance(s, z3.ArithSortRef) and s.name() == "Int":
            return z3.z3printer.to_format("integer")
        return Formatter.pp_sort(self, s)
