from typing import Dict

import z3

from .statements import AssignStmt, ConcurentBlock, IfStmt, SequentialBlock, Statement
from .utils import py2expr


def step(
    curr_state: Dict[z3.ExprRef, z3.ExprRef], stmt: Statement
) -> Dict[z3.ExprRef, z3.ExprRef]:
    post_state = dict(
        [(z3.Const(str(k), k.sort()), v) for (k, v) in curr_state.items()]
    )

    match stmt:
        case AssignStmt(v, rhs):
            rhs = py2expr(rhs)
            rhs = z3.substitute(rhs, *curr_state.items())
            post_state[str(v)] = rhs
        case IfStmt(_, _, _):
            assert False
        case SequentialBlock():
            for s in stmt._stmts:
                post_state = step(post_state, s)
        case ConcurentBlock():
            for s in stmt._stmts:
                tmp_state = step(curr_state, s)
                for k, v in tmp_state.items():
                    if curr_state[k] != v:
                        post_state[k] = v

    return post_state
