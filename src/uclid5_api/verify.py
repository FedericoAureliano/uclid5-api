from typing import Dict

import z3

from .expr import prime, unprimed
from .module import Module
from .statements import AssignStmt, Block, HavocStmt, IfStmt, Statement
from .utils import is_datatype_select, is_var, py2expr


def ensure_consistent(s, end_state, next_as):
    next_as = set(next_as.keys())
    selected_from = set()

    for k in next_as:
        if is_datatype_select(k):
            e = k.children()[0]
            if e not in next_as:
                selected_from.add(e)
                sort = e.sort()
                for i in range(sort.num_constructors()):
                    for j in range(sort.constructor(i).arity()):
                        f = sort.accessor(i, j)
                        if f(e) not in next_as:
                            s.add(f(e) == unprimed(f(e)))

    for v in end_state:
        if v not in next_as and v not in selected_from:
            s.add(v == unprimed(v))


def relate(stmt: Statement) -> Dict[z3.ExprRef, z3.ExprRef]:
    assertions = {}

    def add_to_assertions(x, a):
        if x in assertions:
            raise ValueError(f"Variable {x} is already in assertions!")
        else:
            assertions[x] = a

    match stmt:
        case AssignStmt(v, rhs) if is_var(v):
            rhs = py2expr(rhs, v.sort())
            add_to_assertions(v, v == rhs)
        case AssignStmt(v, rhs) if z3.is_select(v):
            a = v.arg(0)
            index = v.arg(1)
            rhs = py2expr(rhs, v.sort())
            add_to_assertions(a, a == z3.Store(unprimed(a), index, rhs))
        case AssignStmt(v, rhs) if is_datatype_select(v):
            r = v.children()[0]
            rhs = py2expr(rhs, v.sort())
            f = v.decl()
            for i in range(r.sort().num_constructors()):
                for j in range(r.sort().constructor(i).arity()):
                    if f == r.sort().accessor(i, j):
                        add_to_assertions(f(r), f(r) == rhs)
        case HavocStmt(x) if is_var(x):
            fresh = z3.FreshConst(x.sort())
            add_to_assertions(x, x == fresh)
        case IfStmt():
            cond = py2expr(stmt.cond)
            then_as = relate(stmt.then_stmt)
            else_as = relate(stmt.else_stmt)
            for k, v in then_as.items():
                if k in else_as:
                    add_to_assertions(k, z3.If(cond, v, else_as[k]))
                else:
                    add_to_assertions(k, z3.If(cond, v, k == unprimed(k)))
            for k, v in else_as.items():
                if k not in then_as:
                    add_to_assertions(k, z3.If(cond, k == unprimed(k), v))
        case Block():
            for s in stmt._stmts:
                sas = relate(s)
                for k, v in sas.items():
                    add_to_assertions(k, v)
    return assertions


def base_case(m: Module, write_to_prefix: str):
    """
    Base case
    """
    s = z3.Solver()

    start_state = set(m.vars.values())
    end_state = set([prime(v) for v in start_state])

    unrolled = m.init.unrolled(start_state)
    init_as = relate(unrolled)
    s.add(*init_as.values())
    ensure_consistent(s, end_state, init_as)

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
            m = s.model()
            for v in start_state:
                print(f"{prime(v)} = {m[prime(v)]}")
            return False
        s.pop()

    return True


def inductive_step(m: Module, write_to_prefix: str):
    """
    Inductive step
    """
    s = z3.Solver()

    start_state = set(m.vars.values())
    end_state = set([prime(v) for v in start_state])

    next_as = relate(m.next)
    s.add(*next_as.values())
    ensure_consistent(s, end_state, next_as)
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
            m = s.model()
            for v in start_state:
                print(f"{v} = {m[v]}")
                print(f"{prime(v)} = {m[prime(v)]}")
            return False
        s.pop()

    return True


def induction(m: Module, write_to_prefix=""):
    """
    Proof-by-induction
    """
    return base_case(m, write_to_prefix) and inductive_step(m, write_to_prefix)


def bmc(m: Module, k: int, write_to_prefix=""):
    """
    Bounded Model Checking
    """
    s = z3.Solver()

    start_state = set(m.vars.values())
    end_state = set([prime(v) for v in start_state])

    unrolled = m.init.unrolled(start_state)
    init_as = relate(unrolled)
    s.add(*init_as.values())
    ensure_consistent(s, end_state, init_as)

    for i in range(k):
        if i > 0:
            end_state = set([prime(v, i + 1) for v in start_state])
            mapping = [(prime(v), prime(v, i + 1)) for v in start_state] + [
                (v, prime(v, i)) for v in start_state
            ]
            next = m.next.substitute(mapping)
            next_as = relate(next)
            s.add(*next_as.values())
            ensure_consistent(s, end_state, next_as)
        for name, inv in m.invs.items():
            inv = z3.substitute(inv, [(v, prime(v, i + 1)) for v in m.vars.values()])
            s.push()
            s.add(z3.Not(inv))

            if write_to_prefix != "":
                with open(f"{write_to_prefix}_{name}_bmc_{i}.smt2", "w") as f:
                    f.write(s.to_smt2())
                s.pop()
                continue

            if s.check() == z3.sat:
                print(f"Found a counterexample for invariant {name} at step {i}")
                m = s.model()
                for v in start_state:
                    for j in range(1, i + 2):
                        print(f"{prime(v, j)} = {m[prime(v, j)]}")
                return False
            s.pop()

    return True
