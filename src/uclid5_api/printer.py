import z3
from z3.z3printer import Formatter, compose, to_format


class UCLIDFormatter(Formatter):
    def __init__(self):
        Formatter.__init__(self)

    def pp_bv(self, a):
        return to_format(a.as_string() + f"bv{a.size()}")

    def pp_rational(self, a):
        if a.denominator() == 1:
            return compose(to_format(a.numerator()), to_format(".0"))
        return to_format(a.as_decimal(self.precision))

    def pp_sort(self, s):
        if isinstance(s, z3.ArithSortRef) and s.name() == "Int":
            return to_format("integer")
        elif isinstance(s, z3.ArithSortRef) and s.name() == "Real":
            return to_format("real")
        elif isinstance(s, z3.BoolSortRef):
            return to_format("boolean")
        elif isinstance(s, z3.ArraySortRef):
            index = self.pp_sort(s.domain())
            elem = self.pp_sort(s.range())
            return compose(to_format("["), index, to_format("]"), elem)
        elif isinstance(s, z3.BitVecSortRef):
            return to_format(f"bv{s.size()}")
        return Formatter.pp_sort(self, s)
