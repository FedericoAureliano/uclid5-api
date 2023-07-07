import z3


def indent(s):
    """
    Indent a string
    """
    return "\n".join(["  " + line for line in s.split("\n")])


def py2expr(a):
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
