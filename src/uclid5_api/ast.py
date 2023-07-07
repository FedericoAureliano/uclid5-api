"""
Python interface to UCLID5
"""

from dataclasses import dataclass

import z3

from uclid5_api.printer import UCLIDFormatter
from uclid5_api.utils import indent

z3.z3printer._Formatter = UCLIDFormatter()


class Module:
    """
    A UCLID5 module
    """

    def __init__(self, name):
        """
        Create a UCLID5 module
        """
        self.name = name
        self.init = SequentialBlock()
        self.next = ConcurentBlock()
        self._vars = []
        self._invs = []

    def declare_variable(self, name, sort):
        """
        Add a variable to the module
        """
        v = z3.Const(name, sort)
        self._vars.append(v)
        return v

    def add_invariant(self, name, inv):
        """
        Add an invariant to the module
        """
        self._invs.append((name, inv))

    def __str__(self) -> str:
        """
        Return the string representation of the module
        """
        vars = indent("\n".join([f"var {v}: {v.sort()};" for v in self._vars]))
        init = indent("init " + str(self.init))
        next = indent("next " + str(self.next))
        invs = indent(
            "\n".join([f"invariant {name}: {inv};" for (name, inv) in self._invs])
        )
        out = f"module {self.name} {{\n{vars}\n{init}\n{next}\n{invs}\n}}"
        return out


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
