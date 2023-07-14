import copy
from dataclasses import dataclass

import z3

from .expr import prime
from .utils import indent, py2expr


class Statement:
    pass


@dataclass
class AssignStmt(Statement):
    """
    An assignment statement
    """

    v: z3.ExprRef
    rhs: z3.ExprRef


class IfStmt(Statement):
    """
    An if statement
    """

    def __init__(self, cond, then_stmt, else_stmt):
        self.cond = cond
        self.then_stmt = then_stmt
        self.else_stmt = else_stmt

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
            match new_obj._stmts[i]:
                case AssignStmt(v, rhs):
                    new_obj._stmts[i] = AssignStmt(
                        z3.substitute(v, mapping), z3.substitute(rhs, mapping)
                    )
                case IfStmt():
                    new_obj._stmts[i].then_stmt.substitute(mapping)
                    new_obj._stmts[i].else_stmt.substitute(mapping)
                    new_obj._stmts[i].cond = z3.substitute(
                        new_obj._stmts[i].cond, mapping
                    )
                case Block():
                    new_obj._stmts[i].substitute(mapping)
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

    def branch(self, cond):
        """
        Add an if statement to the block and return the two branches
        """
        stmt = IfStmt(cond, SequentialBlock(), SequentialBlock())
        self._stmts.append(stmt)
        return stmt.then_stmt, stmt.else_stmt


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

    def branch(self, cond):
        """
        Add an if statement to the block and return the two branches
        """
        stmt = IfStmt(cond, ConcurentBlock(), ConcurentBlock())
        self._stmts.append(stmt)
        return stmt.then_stmt, stmt.else_stmt
