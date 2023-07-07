"""
Python interface to UCLID5
"""

from dataclasses import dataclass

import z3

from .utils import indent


@dataclass
class Invariant:
    """
    An invariant
    """

    name: str
    pred: z3.ExprRef

    def __str__(self) -> str:
        return f"invariant {self.name}: {self.pred};"


class Statement:
    pass


@dataclass
class AssignStmt(Statement):
    """
    An assignment statement
    """

    v: z3.ExprRef
    rhs: z3.ExprRef

    def __str__(self) -> str:
        return f"{self.v} = {self.rhs};"


@dataclass
class ConcurentAssignStmt(Statement):
    """
    A concurrent assignment statement
    """

    v: z3.ExprRef
    rhs: z3.ExprRef

    def __str__(self) -> str:
        return f"{self.v}' = {self.rhs};"


@dataclass
class IfStmt(Statement):
    """
    An if statement
    """

    cond: z3.ExprRef
    then_stmt: Statement
    else_stmt: Statement

    def __str__(self) -> str:
        then_ = indent(str(self.then_stmt))
        else_ = indent(str(self.else_stmt))
        return f"if ({self.cond}) {{\n{then_}\n}} else {{\n{else_}\n}}"


class Block(Statement):
    pass


class SequentialBlock(Block):
    """
    A sequential block
    """

    def __init__(self):
        """
        Create a sequential block
        """
        self._stmts = []

    def assign(self, v, expr):
        """
        Add a statement to the block
        """
        self._stmts.append(AssignStmt(v, expr))

    def __str__(self) -> str:
        """
        Return the string representation of the block
        """
        out = "{\n"
        for stmt in self._stmts:
            out += f"{indent(str(stmt))}\n"
        out += "}"
        return out


class ConcurentBlock(Block):
    """
    A concurent block
    """

    def __init__(self):
        """
        Create a concurent block
        """
        self._stmts = []

    def assign(self, v, expr):
        """
        Add a statement to the block
        """
        self._stmts.append(ConcurentAssignStmt(v, expr))

    def __str__(self) -> str:
        """
        Return the string representation of the block
        """
        out = "{\n"
        for stmt in self._stmts:
            out += f"{indent(str(stmt))}\n"
        out += "}"
        return out
