import z3


def prime(x, i=1):
    """
    Return the primed version of the variable
    """
    if (
        isinstance(x, z3.ExprRef)
        and z3.is_const(x)
        and x.decl().kind() == z3.Z3_OP_UNINTERPRETED
    ):
        return z3.Const(x.decl().name() + "'" * i, x.sort())
