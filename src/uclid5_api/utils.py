import z3


def indent(s):
    """
    Indent a string
    """
    return "\n".join(["  " + line for line in s.split("\n")])


def is_var(x):
    return z3.is_const(x) and x.decl().kind() == z3.Z3_OP_UNINTERPRETED


def is_datatype_select(x):
    if not (
        z3.is_app(x)
        and x.num_args() == 1
        and isinstance(x.children()[0].sort(), z3.DatatypeSortRef)
    ):
        return False

    dt = x.children()[0].sort()
    for i in range(dt.num_constructors()):
        for j in range(dt.constructor(i).arity()):
            if x.decl() == dt.accessor(i, j):
                return True

    return False


def is_datatype_construct(x):
    if not (
        z3.is_app(x)
        and x.num_args() >= 1
        and isinstance(x.decl().range(), z3.DatatypeSortRef)
    ):
        return False

    dt = x.decl().range()
    for i in range(dt.num_constructors()):
        if x.decl() == dt.constructor(i):
            return True

    return False


def is_datatype_recognize(x):
    if not (
        z3.is_app(x)
        and x.num_args() == 1
        and isinstance(x.children()[0].sort(), z3.DatatypeSortRef)
    ):
        return False

    dt = x.children()[0].sort()
    for i in range(dt.num_constructors()):
        if x.decl() == dt.recognizer(i):
            return True

    return False


def py2expr(a, sort=None):
    if sort is None:
        if isinstance(a, bool):
            return z3.BoolVal(a)
        if isinstance(a, int):
            return z3.IntVal(a)
        if isinstance(a, float):
            return z3.RealVal(a)
        if isinstance(a, str):
            return z3.StringVal(a)
        if z3.is_expr(a):
            return a
        raise Exception(f"Could not automatically cast {a}")
    else:
        if z3.is_expr(a) and a.sort() == sort:
            return a
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
