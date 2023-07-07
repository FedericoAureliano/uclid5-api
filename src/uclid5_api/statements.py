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

    def condition(self, cond):
        """
        Add an if statement to the block and return the two branches
        """
        stmt = IfStmt(cond, SequentialBlock(), SequentialBlock())
        self._stmts.append(stmt)
        return stmt.then_stmt, stmt.else_stmt

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

    def condition(self, cond):
        """
        Add an if statement to the block and return the two branches
        """
        stmt = IfStmt(cond, ConcurentBlock(), ConcurentBlock())
        self._stmts.append(stmt)
        return stmt.then_stmt, stmt.else_stmt

    def __str__(self) -> str:
        """
        Return the string representation of the block
        """
        out = "{\n"
        for stmt in self._stmts:
            match stmt:
                case AssignStmt(v, rhs):
                    out += f"{indent(str(v))}' = {str(rhs)};\n"
                case IfStmt():
                    out += f"{indent(str(stmt))}\n"
        out += "}"
        return out