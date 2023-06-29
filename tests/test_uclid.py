import z3

from uclid5_api import Module

__author__ = "FedericoAureliano"
__copyright__ = "FedericoAureliano"
__license__ = "MIT"


def test():
    m = Module("test")
    x = m.declare_variable("x", z3.IntSort())
    y = m.declare_variable("y", z3.IntSort())
    m.init.assign(x, 0)
    m.init.assign(y, 0)
    m.next.assign(x, x + 1)
    m.next.assign(y, y + 1)
    m.add_invariant("inv1", x < y)
    print(m)
    assert True
