from typing import List, Set, Tuple

import z3

from .expr import prime, unprimed
from .module import Module
from .statements import AssignStmt, Block, IfStmt, Statement
from .utils import is_var, py2expr


def relate(
    stmt: Statement, state: Set[z3.ExprRef]
) -> Tuple[List[z3.ExprRef], Set[z3.ExprRef]]:
    assertions = []
    modified = set()

    match stmt:
        case AssignStmt(v, rhs) if is_var(v):
            modified.add(unprimed(v))
            rhs = py2expr(rhs, v.sort())
            assertions.append(v == rhs)
        case AssignStmt(v, rhs) if z3.is_select(v):
            a = v.arg(0)
            index = v.arg(1)
            rhs = py2expr(rhs, v.sort())
            modified.add(unprimed(a))
            assertions.append(a == z3.Store(unprimed(a), index, rhs))
        case IfStmt():
            cond = py2expr(stmt.cond)
            then_as, then_ms = relate(stmt.then_stmt, state)
            else_as, else_ms = relate(stmt.else_stmt, state)
            for a in then_as:
                assertions.append(z3.Implies(cond, a))
            for m in then_ms:
                modified.add(unprimed(m))
            for a in else_as:
                assertions.append(z3.Implies(z3.Not(cond), a))
            for m in else_ms:
                modified.add(unprimed(m))
        case Block():
            for s in stmt._stmts:
                sas, sms = relate(s, state)
                assertions += sas
                modified |= sms

    return assertions, modified


def base_case(m: Module, write_to_prefix: str):
    """
    Base case
    """
    s = z3.Solver()

    state = set(m.vars.values())
    unrolled = m.init.unrolled(state)
    init_as, modified = relate(unrolled, state)
    s.add(init_as)
    for v in state.difference(modified):
        s.add(prime(v) == v)

    for name, inv in m.invs.items():
        inv = z3.substitute(inv, [(v, prime(v)) for v in m.vars.values()])
        s.push()
        s.add(z3.Not(inv))

        if write_to_prefix != "":
            with open(f"{write_to_prefix}_{name}_base.smt2", "w") as f:
                f.write(s.to_smt2())
            s.pop()
            continue

        if s.check() == z3.sat:
            print(f"Found a counterexample at the base case for invariant {name}")
            print(s.model())
            return False
        s.pop()

    return True


def inductive_step(m: Module, write_to_prefix: str):
    """
    Inductive step
    """
    s = z3.Solver()
    state = set(m.vars.values())
    next_as, modified = relate(m.next, state)
    s.add(next_as)
    for v in state.difference(modified):
        s.add(prime(v) == v)
    for name, inv_before in m.invs.items():
        inv_after = z3.substitute(inv_before, [(v, prime(v)) for v in m.vars.values()])
        s.push()
        s.add(inv_before)
        s.add(z3.Not(inv_after))

        if write_to_prefix != "":
            with open(f"{write_to_prefix}_{name}_induction.smt2", "w") as f:
                f.write(s.to_smt2())
            s.pop()
            continue

        if s.check() == z3.sat:
            print(f"Found a counterexample for invariant {name} in the inductive step")
            print(s.model())
            return False
        s.pop()

    return True


def induction(m: Module, write_to_prefix=""):
    """
    Proof-by-induction
    """
    return base_case(m, write_to_prefix) and inductive_step(m, write_to_prefix)
