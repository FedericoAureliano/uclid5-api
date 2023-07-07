from typing import Dict

import z3

from .module import Module
from .statements import AssignStmt, ConcurentBlock, IfStmt, SequentialBlock, Statement
from .utils import indent, py2expr


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
            post_state[v] = rhs
        case IfStmt():
            cond = py2expr(stmt.cond)
            cond = z3.substitute(cond, *curr_state.items())
            then_state = step(curr_state, stmt.then_stmt)
            else_state = step(curr_state, stmt.else_stmt)
            for k, v in then_state.items():
                if else_state[k] is not v:
                    post_state[k] = z3.If(cond, v, else_state[k])
        case SequentialBlock():
            for s in stmt._stmts:
                post_state = step(post_state, s)
        case ConcurentBlock():
            for s in stmt._stmts:
                tmp_state = step(curr_state, s)
                for k, v in tmp_state.items():
                    if curr_state[k] is not v:
                        post_state[k] = v

    return post_state


def bmc(m: Module, k: int) -> bool:
    """
    Bounded model checking
    """
    assert k > 0

    # create a solver
    s = z3.Solver()

    # create a state
    states = [dict([(v, z3.Const(str(v), v.sort())) for v in m.vars])]
    states.append(step(states[-1], m.init))

    for i in range(k):
        for name, inv in m.invs.items():
            s.push()
            s.add(z3.substitute(z3.Not(py2expr(inv)), *states[-1].items()))

            check = s.check()
            if check == z3.sat:
                print(f"Found a counterexample at step {i} for invariant {name}!")
                model = s.model()
                for j in range(1, len(states)):
                    print(indent(f"Step {j - 1}:"))
                    for x, v in states[j].items():
                        print(indent(indent(f"{x} := {model.eval(v)}")))
                return False
            elif check == z3.unknown:
                print("Unknown")
                return False

            s.pop()

        states.append(step(states[-1], m.next))

    print("No counterexample found after unrolling {k} times!")
    return True


def induction(m: Module):
    """
    Proof by induction
    """

    # create a solver
    s = z3.Solver()

    # create the states before init, after init, and after next
    before = dict([(v, z3.Const(str(v), v.sort())) for v in m.vars])
    after_init = step(before, m.init)
    after_next = step(before, m.next)

    # check that the invariant holds for the base case
    for name, inv in m.invs.items():
        s.push()
        s.add(z3.substitute(z3.Not(py2expr(inv)), *after_init.items()))
        check = s.check()
        if check == z3.sat:
            print(f"Found a counterexample at the base case for invariant {name}!")
            model = s.model()
            print(indent("Before init:"))
            for x, v in before.items():
                print(indent(indent(f"{x} := {model.eval(v)}")))
            print(indent("After init:"))
            for x, v in before.items():
                print(indent(indent(f"{x} := {model.eval(v)}")))
            return False
        elif check == z3.unknown:
            print("Unknown")
            return False
        s.pop()

    # check that the invariant holds for the inductive step
    for name, inv in m.invs.items():
        s.push()
        for name, inv in m.invs.items():
            s.add(z3.substitute(py2expr(inv), *before.items()))
        s.add(z3.substitute(z3.Not(py2expr(inv)), *after_next.items()))
        check = s.check()
        if check == z3.sat:
            print(f"Found a counterexample at the inductive step for invariant {name}!")
            model = s.model()
            print(indent("Before next:"))
            for x, v in before.items():
                print(indent(indent(f"{x} := {model.eval(v)}")))
            print(indent("After next:"))
            for x, v in before.items():
                print(indent(indent(f"{x} := {model.eval(v)}")))
            return False
        elif check == z3.unknown:
            print("Unknown")
            return False
        s.pop()

    print("Proof by induction passed!")
    return True
