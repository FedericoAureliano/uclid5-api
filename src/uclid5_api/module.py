import copy

import z3

from .statements import ConcurentBlock, Instance, SequentialBlock
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
        self.instances = {}

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

    def instantiate(self, module, name):
        """
        Add a module instance
        """
        m = copy.deepcopy(module)
        i = Instance(name, m)
        self.instances[i] = i
        return i

    def __str__(self) -> str:
        """
        Return the string representation of the module
        """
        submodules = "\n".join([str(m.module) for m in self.instances.values()]) + "\n"
        vars = (
            (
                indent("\n".join([f"var {v}: {v.sort()};" for v in self.vars.values()]))
                + "\n"
            )
            if self.vars.keys()
            else ""
        )
        instances = (
            (
                indent(
                    "\n".join(
                        [
                            f"instance {i.name}: {i.module.name}();"
                            for i in self.instances.values()
                        ]
                    )
                )
                + "\n"
            )
            if self.instances.keys()
            else ""
        )
        init = indent("init " + str(self.init)) + "\n" if self.init._stmts else ""
        next = indent("next " + str(self.next)) + "\n" if self.next._stmts else ""
        invs = (
            indent("\n".join([f"invariant {n}: {i};" for (n, i) in self.invs.items()]))
            + "\n"
            if self.invs.keys()
            else ""
        )
        out = (
            submodules + f"module {self.name} {{\n{vars}{instances}{init}{next}{invs}}}"
        )
        return out
