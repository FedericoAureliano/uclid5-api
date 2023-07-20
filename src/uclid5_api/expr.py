import z3

from .utils import is_datatype_select, is_var


def prime(x):
    """
    Return the primed version of the variable
    """
    match x:
        case z3.ExprRef() if is_var(x):
            return z3.Const(x.decl().name() + "'", x.sort())
        case z3.ExprRef() if z3.is_select(x):
            return z3.Select(prime(x.arg(0)), x.arg(1))
        case z3.ExprRef() if is_datatype_select(x):
            selector = x.decl()
            record = x.arg(0)
            return selector(prime(record))
        case _:
            raise Exception(f"Cannot prime {x}")


def unprimed(x):
    """
    Return the unprimed version of the variable
    """
    match x:
        case z3.ExprRef() if is_var(x):
            if x.decl().name().endswith("'"):
                return z3.Const(x.decl().name()[:-1], x.sort())
            else:
                return x
        case z3.ExprRef() if z3.is_select(x):
            return z3.Select(unprimed(x.arg(0)), x.arg(1))
        case _:
            raise Exception(f"Cannot unprime {x}")
