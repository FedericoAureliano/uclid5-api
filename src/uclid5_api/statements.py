import copy
from dataclasses import dataclass

import z3

from .expr import prime
from .utils import indent, is_var, py2expr


class Statement:
    pass


@dataclass
class AssignStmt(Statement):
    """
    An assignment statement
    """

    v: z3.ExprRef
    rhs: z3.ExprRef

    def substitute(self, mapping):
        return AssignStmt(
            z3.substitute(self.v, mapping), z3.substitute(self.rhs, mapping)
        )


@dataclass
class HavocStmt(Statement):
    """
    A havoc statement
    """

    x: z3.ExprRef

    def substitute(self, mapping):
        return HavocStmt(z3.substitute(self.x, mapping))


class IfStmt(Statement):
    """
    An if statement
    """

    def __init__(self, cond, then_stmt, else_stmt):
        self.cond = cond
        self.then_stmt = then_stmt
        self.else_stmt = else_stmt

    def substitute(self, mapping):
        """
        Substitute variables in the block
        """
        new_then = self.then_stmt.substitute(mapping)
        new_else = self.else_stmt.substitute(mapping)
        new_cond = z3.substitute(self.cond, mapping)
        return IfStmt(new_cond, new_then, new_else)

    def __str__(self) -> str:
        then_ = str(self.then_stmt)
        else_ = str(self.else_stmt)
        return f"if ({self.cond}) {then_}\nelse {else_}"


class Block(Statement):
    def __init__(self):
        self._stmts = []

    def __str__(self) -> str:
        """
        Return the string representation of the block
        """
        out = "{\n"
        for stmt in self._stmts:
            match stmt:
                case AssignStmt(v, rhs):
                    out += f"{indent(str(v))} = {str(rhs)};\n"
                case HavocStmt(x):
                    out += f"havoc {str(x)};\n"
                case IfStmt():
                    out += f"{indent(str(stmt))}\n"
        out += "}"
        return out

    def substitute(self, mapping):
        """
        Substitute variables in the block
        """
        new_obj = copy.deepcopy(self)
        for i in range(len(new_obj._stmts)):
            new_obj._stmts[i] = new_obj._stmts[i].substitute(mapping)
        return new_obj


class SequentialBlock(Block):
    """
    A sequential block
    """

    def __init__(self):
        """
        Create a sequential block
        """
        Block.__init__(self)

    def assign(self, v, expr):
        """
        Add a statement to the block
        """
        self._stmts.append(AssignStmt(v, py2expr(expr, v.sort())))

    def havoc(self, x):
        """
        Add a havoc statement to the block
        """
        self._stmts.append(HavocStmt(x))

    def branch(self, cond):
        """
        Add an if statement to the block and return the two branches
        """
        stmt = IfStmt(cond, SequentialBlock(), SequentialBlock())
        self._stmts.append(stmt)
        return stmt.then_stmt, stmt.else_stmt

    def unrolled(self, start):
        new_stmts = []
        tmp_states = [
            dict([(v, z3.Const(v.decl().name() + "_tmp", v.sort())) for v in start])
        ]

        latest = tmp_states[-1]

        for v in start:
            new_stmts.append(AssignStmt(tmp_states[-1][v], v))

        for stmt in self._stmts:
            tmp_states.append(
                dict([(k, prime(v)) for (k, v) in tmp_states[-1].items()])
            )
            curr = list(tmp_states[-1].items())
            prev = list(tmp_states[-2].items())
            match stmt:
                case AssignStmt(v, rhs) if is_var(v):
                    new_lhs = z3.substitute(v, curr)
                    new_rhs = z3.substitute(rhs, prev)
                    new_stmts.append(AssignStmt(new_lhs, new_rhs))
                    latest[v] = new_lhs
                case AssignStmt(v, rhs) if z3.is_select(v):
                    new_a = z3.substitute(v.arg(0), curr)
                    new_index = z3.substitute(v.arg(1), prev)
                    new_rhs = z3.substitute(rhs, prev)
                    new_stmts.append(AssignStmt(new_a[new_index], new_rhs))
                    latest[v.arg(0)] = new_a
                case HavocStmt(x):
                    new_x = z3.substitute(x, curr)
                    new_stmts.append(HavocStmt(new_x))
                    latest[x] = new_x
                case IfStmt():
                    cond = stmt.cond
                    then_stmt = stmt.then_stmt
                    else_stmt = stmt.else_stmt

                    new_cond = z3.substitute(cond, prev)
                    new_then = then_stmt.substitute(prev).unrolled(
                        [v for (_, v) in prev]
                    )
                    new_else = else_stmt.substitute(prev).unrolled(
                        [v for (_, v) in prev]
                    )
                    new_stmts.append(IfStmt(new_cond, new_then, new_else))
                case _:
                    raise Exception(f"Cannot unroll {stmt}")

        for v, n in latest.items():
            new_stmts.append(AssignStmt(prime(v), n))

        new_block = SequentialBlock()
        new_block._stmts = new_stmts
        return new_block


class ConcurentBlock(Block):
    """
    A concurent block
    """

    def __init__(self):
        """
        Create a concurent block
        """
        Block.__init__(self)

    def assign(self, v, expr):
        """
        Add a statement to the block
        """
        self._stmts.append(AssignStmt(prime(v), py2expr(expr, v.sort())))

    def havoc(self, x):
        """
        Add a havoc statement to the block
        """
        self._stmts.append(HavocStmt(prime(x)))

    def branch(self, cond):
        """
        Add an if statement to the block and return the two branches
        """
        stmt = IfStmt(cond, ConcurentBlock(), ConcurentBlock())
        self._stmts.append(stmt)
        return stmt.then_stmt, stmt.else_stmt
