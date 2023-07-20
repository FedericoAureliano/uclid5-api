import z3
from z3.z3printer import Formatter, compose, to_format

from .types import this
from .utils import is_datatype_construct, is_datatype_recognize, is_datatype_select


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
        elif isinstance(s, z3.DatatypeSortRef):
            if s.name().startswith("Record_"):
                fields = [s.accessor(0, i) for i in range(s.constructor(0).arity())]
                names = [f.name() for f in fields]
                types = [f.range() for f in fields]
                fields = [f"{n}: {t}" for (n, t) in zip(names, types)]
                return compose(
                    to_format("record {"), to_format(", ".join(fields)), to_format("}")
                )
            elif s.name().startswith("Enum_"):
                variants = [
                    s.constructor(i).name() for i in range(s.num_constructors())
                ]
                return compose(
                    to_format("enum {"), to_format(", ".join(variants)), to_format("}")
                )
            else:
                constructors = []
                for i in range(s.num_constructors()):
                    c = s.constructor(i).name()
                    args = [s.accessor(i, j) for j in range(s.constructor(i).arity())]
                    sels = []
                    for a in args:
                        if a.range().name() == s.name():
                            sels.append(f"{a.name()}: {this()}")
                        else:
                            sels.append(f"{a.name()}: {a.range()}")
                    constructors.append(f"{c}({', '.join(sels)})" if sels else c)
                return compose(
                    to_format(f"datatype {s.name()} = {{"),
                    to_format(" | ".join(constructors)),
                    to_format("}"),
                )
        return Formatter.pp_sort(self, s)

    def pp_app(self, a, d, xs):
        if is_datatype_select(a):
            return to_format(f"{a.arg(0).decl().name()}.{a.decl().name()}")
        if is_datatype_recognize(a):
            return to_format(f"{a.arg(0).decl().name()} is {a.decl().params()[0]}")
        elif is_datatype_construct(a):
            if a.num_args() == 0:
                return to_format(f"{a.decl().name()}")
            if a.decl().range().name().startswith("Enum_"):
                return to_format(f"{a.decl().name()}({a.arg(0)})")
            if a.decl().range().name().startswith("Record_"):
                record = a.decl().range()
                fields = [
                    str(record.accessor(0, i))
                    for i in range(record.constructor(0).arity())
                ]
                values = [str(a.arg(i)) for i in range(a.num_args())]
                fields = [f"{n} = {v}" for (n, v) in zip(fields, values)]
                return compose(
                    to_format("{"), to_format(", ".join(fields)), to_format("}")
                )
            else:
                record = a.decl().range()
                values = [str(a.arg(i)) for i in range(a.num_args())]
                return compose(
                    to_format(f"{a.decl()}("),
                    to_format(", ".join(values)),
                    to_format(")"),
                )

        return Formatter.pp_app(self, a, d, xs)
