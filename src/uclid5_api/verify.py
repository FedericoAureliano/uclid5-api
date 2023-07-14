from typing import List

import z3

from .expr import prime
from .module import Module
from .statements import AssignStmt, Block, IfStmt, Statement
from .utils import py2expr


def relate(stmt: Statement) -> List[z3.ExprRef]:
    assertions = []
    match stmt:
        case AssignStmt(v, rhs):
            rhs = py2expr(rhs)
            assertions.append(v == rhs)
        case IfStmt():
            cond = py2expr(stmt.cond)
            for a in relate(stmt.then_stmt):
                assertions.append(z3.Implies(cond, a))
            for a in relate(stmt.else_stmt):
                assertions.append(z3.Implies(z3.Not(cond), a))
        case Block():
            for s in stmt._stmts:
                assertions += relate(s)

    return assertions


def bmc(m: Module, k: int) -> bool:
    """
    Bounded model checking
    """
    assert k > 0
    s = z3.Solver()

    s.add(relate(m.init))
    for i in range(k):
        if i > 0:
            next = m.next.substitute(
                [(prime(v), prime(v, i)) for v in m.vars.values()]
                + [(v, prime(v, i - 1)) for v in m.vars.values()]
            )
            s.add(relate(next))
        for name, inv in m.invs.items():
            inv = z3.substitute(inv, [(v, prime(v, i)) for v in m.vars.values()])
            s.push()
            s.add(z3.Not(inv))
            if s.check() == z3.sat:
                print(f"Found a counterexample at step {i} for invariant {name}")
                return False
            s.pop()

    return True


def base_case(m: Module):
    """
    Base case
    """
    s = z3.Solver()
    s.add(relate(m.init))
    for name, inv in m.invs.items():
        s.push()
        s.add(z3.Not(inv))
        if s.check() == z3.sat:
            print(f"Found a counterexample for invariant {name} in the base case")
            return False
        s.pop()
    return True


def inductive_step(m: Module):
    """
    Inductive step
    """
    s = z3.Solver()
    s.add(relate(m.next))
    for name, inv_before in m.invs.items():
        inv_after = z3.substitute(inv_before, [(v, prime(v)) for v in m.vars.values()])
        s.push()
        s.add(inv_before)
        s.add(z3.Not(inv_after))
        if s.check() == z3.sat:
            print(f"Found a counterexample for invariant {name} in the inductive step")
            return False
        s.pop()
    return True


def induction(m: Module):
    """
    Proof-by-induction
    """
    return base_case(m) and inductive_step(m)
