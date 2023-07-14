import z3


def indent(s):
    """
    Indent a string
    """
    return "\n".join(["  " + line for line in s.split("\n")])


def py2expr(a, sort=None):
    print(f"a: {a}, sort: {sort}")
    if sort is None:
        if isinstance(a, bool):
            return z3.BoolVal(a)
        if isinstance(a, int):
            return z3.IntVal(a)
        if isinstance(a, float):
            return z3.RealVal(a)
        if isinstance(a, str):
            return z3.StringVal(a)
        if z3.is_expr(a) and a.sort() == sort:
            return a
        raise Exception(f"Cannot convert {a} to an expression of sort {sort}")
    elif z3.is_expr(a):
        return a
    else:
        if z3.is_bv_sort(sort):
            return z3.BitVecVal(a, sort.size())
        elif sort == z3.IntSort():
            return z3.IntVal(a)
        elif sort == z3.BoolSort():
            return z3.BoolVal(a)
        elif sort == z3.RealSort():
            return z3.RealVal(a)
        elif sort == z3.StringSort():
            return z3.StringVal(a)
        else:
            raise Exception(f"Cannot convert {a} to an expression of sort {sort}")
