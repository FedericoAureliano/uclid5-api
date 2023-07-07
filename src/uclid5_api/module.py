import z3

from .statements import ConcurentBlock, SequentialBlock
from .utils import indent


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
        self.vars = {}
        self.invs = {}

    def declare_var(self, name, sort):
        """
        Add a variable to the module
        """
        v = z3.Const(name, sort)
        self.vars[v] = v
        return v

    def assert_invariant(self, name, inv):
        """
        Add an invariant to the module
        """
        self.invs[name] = inv

    def __str__(self) -> str:
        """
        Return the string representation of the module
        """
        vars = (
            indent("\n".join([f"var {v}: {v.sort()};" for v in self.vars.values()]))
            + "\n"
        )
        init = indent("init " + str(self.init)) + "\n" if self.init._stmts else ""
        next = indent("next " + str(self.next)) + "\n" if self.init._stmts else ""
        invs = (
            indent(
                "\n".join([f"invariant {n}: {i};" for (n, i) in self.invs.items()])
                + "\n"
            )
            if self.invs.keys()
            else ""
        )
        out = f"module {self.name} {{\n{vars}{init}{next}{invs}}}"
        return out
