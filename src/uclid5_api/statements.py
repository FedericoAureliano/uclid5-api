"""
Python interface to UCLID5
"""

from dataclasses import dataclass

import z3

from .utils import indent


class Statement:
    pass


@dataclass
class AssignStmt(Statement):
    """
    An assignment statement
    """

    v: z3.ExprRef
    rhs: z3.ExprRef


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
    def __init__(self):
        self._stmts = []


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
        self._stmts.append(AssignStmt(v, expr))

    def __str__(self) -> str:
        """
        Return the string representation of the block
        """
        out = "{\n"
        for stmt in self._stmts:
            match stmt:
                case AssignStmt(v, rhs):
                    out += f"{indent(str(v))} = {str(rhs)};\n"
                case IfStmt(_, _, _):
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
        self._stmts.append(AssignStmt(v, expr))

    def __str__(self) -> str:
        """
        Return the string representation of the block
        """
        out = "{\n"
        for stmt in self._stmts:
            match stmt:
                case AssignStmt(v, rhs):
                    out += f"{indent(str(v))}' = {str(rhs)};\n"
                case IfStmt(_, _, _):
                    out += f"{indent(str(stmt))}\n"
        out += "}"
        return out
