import z3
from z3.z3printer import Formatter


class UCLIDFormatter(Formatter):
    def __init__(self):
        Formatter.__init__(self)

    def pp_sort(self, s):
        if isinstance(s, z3.ArithSortRef) and s.name() == "Int":
            return z3.z3printer.to_format("integer")
        elif isinstance(s, z3.ArithSortRef) and s.name() == "Real":
            return z3.z3printer.to_format("real")
        elif isinstance(s, z3.BoolSortRef):
            return z3.z3printer.to_format("boolean")
        elif isinstance(s, z3.ArraySortRef):
            index = self.pp_sort(s.domain())
            elem = self.pp_sort(s.range())
            return z3.z3printer.compose(
                z3.z3printer.to_format("["), index, z3.z3printer.to_format("]"), elem
            )
        elif isinstance(s, z3.BitVecSortRef):
            return z3.z3printer.to_format(f"bv{s.size()}")
        return Formatter.pp_sort(self, s)
