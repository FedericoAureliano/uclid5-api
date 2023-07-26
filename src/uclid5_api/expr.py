import z3

from .utils import is_datatype_select, is_var


def prime(x, i=1):
    """
    Return the primed version of the variable
    """
    match x:
        case z3.ExprRef() if is_var(x):
            return z3.Const(x.decl().name() + "'" * i, x.sort())
        case z3.ExprRef() if z3.is_select(x):
            return z3.Select(prime(x.arg(0), i), x.arg(1))
        case z3.ExprRef() if is_datatype_select(x):
            selector = x.decl()
            record = x.arg(0)
            return selector(prime(record, i))
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
        case z3.ExprRef() if is_datatype_select(x):
            selector = x.decl()
            record = x.arg(0)
            return selector(unprimed(record))
        case _:
            raise Exception(f"Cannot unprime {x}")


def Or(*args):
    """
    Return the disjunction of the arguments
    """
    return z3.Or(*args)


def And(*args):
    """
    Return the conjunction of the arguments
    """
    return z3.And(*args)


def Implies(a, b):
    """
    Return the implication of a and b
    """
    return z3.Implies(a, b)


def Not(a):
    """
    Return the negation of a
    """
    return z3.Not(a)


def Ite(cond, then_, else_):
    """
    Return the if-then-else of cond, then_, and else_
    """
    return z3.If(cond, then_, else_)
